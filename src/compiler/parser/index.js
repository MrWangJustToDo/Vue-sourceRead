/* @flow */

import he from "he";
import { parseHTML } from "./html-parser";
import { parseText } from "./text-parser";
import { parseFilters } from "./filter-parser";
import { genAssignmentCode } from "../directives/model";
import { extend, cached, no, camelize, hyphenate } from "shared/util";
import { isIE, isEdge, isServerRendering } from "core/util/env";

import {
  addProp,
  addAttr,
  baseWarn,
  addHandler,
  addDirective,
  getBindingAttr,
  getAndRemoveAttr,
  getRawBindingAttr,
  pluckModuleFunction,
  getAndRemoveAttrByRegex,
} from "../helpers";

// 正则表达式图解
// https://regexper.com/#
// https://jex.im/regulex/#!flags=&re=

// 匹配 v-on: 或者 @
export const onRE = /^@|^v-on:/;

// 匹配 v- | @ | : | . | # 开头的内容
export const dirRE = process.env.VBIND_PROP_SHORTHAND
  ? /^v-|^@|^:|^\.|^#/
  : /^v-|^@|^:|^#/;

// 匹配 for (let key in/of keys) {} 这种循环
export const forAliasRE = /([\s\S]*?)\s+(?:in|of)\s+([\s\S]*)/;
// 匹配 迭代器？？
export const forIteratorRE = /,([^,\}\]]*)(?:,([^,\}\]]*))?$/;
// 匹配 (开头  或者  )结尾
const stripParensRE = /^\(|\)$/g;
// 匹配 [XXXXXX] 字符串
const dynamicArgRE = /^\[.*\]$/;

const argRE = /:(.*)$/;
export const bindRE = /^:|^\.|^v-bind:/;
const propBindRE = /^\./;
const modifierRE = /\.[^.\]]+(?=[^\]]*$)/g;

const slotRE = /^v-slot(:|$)|^#/;

const lineBreakRE = /[\r\n]/;
const whitespaceRE = /[ \f\t\r\n]+/g;

const invalidAttributeRE = /[\s"'<>\/=]/;

const decodeHTMLCached = cached(he.decode);

export const emptySlotScopeToken = `_empty_`;

// configurable state
export let warn: any;
let delimiters;
let transforms;
let preTransforms;
let postTransforms;
let platformIsPreTag;
let platformMustUseProp;
let platformGetTagNamespace;
let maybeComponent;

// 创建一个语法树节点   递归解析模板  生成语法树
export function createASTElement(
  tag: string,
  attrs: Array<ASTAttr>,
  parent: ASTElement | void
): ASTElement {
  return {
    type: 1,
    tag,
    attrsList: attrs,
    attrsMap: makeAttrsMap(attrs),
    rawAttrsMap: {},
    parent,
    children: [],
  };
}

/**
 * Convert HTML string to AST.
 */
export function parse(
  template: string,
  options: CompilerOptions
): ASTElement | void {
  warn = options.warn || baseWarn;
  // 这些都是方法  判断返回布尔值
  platformIsPreTag = options.isPreTag || no;
  platformMustUseProp = options.mustUseProp || no;
  platformGetTagNamespace = options.getTagNamespace || no;
  const isReservedTag = options.isReservedTag || no;
  // 判断是不是一个组件
  maybeComponent = (el: ASTElement) =>
    !!(
      el.component ||
      el.attrsMap[":is"] ||
      el.attrsMap["v-bind:is"] ||
      !(el.attrsMap.is ? isReservedTag(el.attrsMap.is) : isReservedTag(el.tag))
    );

  // 应该是根据name选择出其中的方法
  transforms = pluckModuleFunction(options.modules, "transformNode");
  preTransforms = pluckModuleFunction(options.modules, "preTransformNode");
  postTransforms = pluckModuleFunction(options.modules, "postTransformNode");

  delimiters = options.delimiters;

  const stack = [];
  const preserveWhitespace = options.preserveWhitespace !== false;
  const whitespaceOption = options.whitespace;
  let root;
  let currentParent;
  let inVPre = false;
  let inPre = false;
  let warned = false;

  function warnOnce(msg, range) {
    if (!warned) {
      warned = true;
      warn(msg, range);
    }
  }

  function closeElement(element) {
    // 移除当前节点children中末尾的空白节点
    trimEndingWhitespace(element);
    // inVPre = false && element.processed = (undefined || false)
    if (!inVPre && !element.processed) {
      // 单标签并且v-pre  不执行这个逻辑
      // 不光是单标签  从栈中拿出节点闭合时也执行
      element = processElement(element, options);
    }
    // tree management
    if (!stack.length && element !== root) {
      // allow root elements with v-if, v-else-if and v-else
      if (root.if && (element.elseif || element.else)) {
        if (process.env.NODE_ENV !== "production") {
          checkRootConstraints(element);
        }
        addIfCondition(root, {
          exp: element.elseif,
          block: element,
        });
      } else if (process.env.NODE_ENV !== "production") {
        warnOnce(
          `Component template should contain exactly one root element. ` +
            `If you are using v-if on multiple elements, ` +
            `use v-else-if to chain them instead.`,
          { start: element.start }
        );
      }
    }
    if (currentParent && !element.forbidden) {
      if (element.elseif || element.else) {
        processIfConditions(element, currentParent);
      } else {
        if (element.slotScope) {
          // scoped slot
          // keep it in the children list so that v-else(-if) conditions can
          // find it as the prev node.
          const name = element.slotTarget || '"default"';
          (currentParent.scopedSlots || (currentParent.scopedSlots = {}))[
            name
          ] = element;
        }
        currentParent.children.push(element);
        element.parent = currentParent;
      }
    }

    // final children cleanup
    // filter out scoped slots
    element.children = element.children.filter((c) => !(c: any).slotScope);
    // remove trailing whitespace node again
    trimEndingWhitespace(element);

    // check pre state
    if (element.pre) {
      inVPre = false;
    }
    if (platformIsPreTag(element.tag)) {
      inPre = false;
    }
    // apply post-transforms
    for (let i = 0; i < postTransforms.length; i++) {
      postTransforms[i](element, options);
    }
  }

  // 移除children中末尾的空白节点
  function trimEndingWhitespace(el) {
    // remove trailing whitespace node
    if (!inPre) {
      let lastNode;
      while (
        (lastNode = el.children[el.children.length - 1]) &&
        lastNode.type === 3 &&
        lastNode.text === " "
      ) {
        el.children.pop();
      }
    }
  }

  function checkRootConstraints(el) {
    if (el.tag === "slot" || el.tag === "template") {
      warnOnce(
        `Cannot use <${el.tag}> as component root element because it may ` +
          "contain multiple nodes.",
        { start: el.start }
      );
    }
    if (el.attrsMap.hasOwnProperty("v-for")) {
      warnOnce(
        "Cannot use v-for on stateful component root element because " +
          "it renders multiple elements.",
        el.rawAttrsMap["v-for"]
      );
    }
  }

  // 解析出的语法树
  /*
  {type: 1, tag: "div", attrsList: Array(0), attrsMap: {…}, rawAttrsMap: {…}, …}
    attrsList: []
    attrsMap: {}
    children: (3) [{…}, {…}, {…}]
    end: 349
    parent: undefined
    plain: true
    rawAttrsMap: {}
    start: 0
    static: false
    staticRoot: false
    tag: "div"
  */
  parseHTML(template, {
    warn,
    expectHTML: options.expectHTML,
    isUnaryTag: options.isUnaryTag,
    canBeLeftOpenTag: options.canBeLeftOpenTag,
    shouldDecodeNewlines: options.shouldDecodeNewlines,
    shouldDecodeNewlinesForHref: options.shouldDecodeNewlinesForHref,
    shouldKeepComment: options.comments,
    outputSourceRange: options.outputSourceRange,
    start(tag, attrs, unary, start, end) {
      // check namespace.
      // inherit parent ns if there is one
      const ns =
        (currentParent && currentParent.ns) || platformGetTagNamespace(tag);

      // handle IE svg bug
      /* istanbul ignore if */
      if (isIE && ns === "svg") {
        attrs = guardIESVGBug(attrs);
      }

      // 基于传入的属性创建当前的语法树节点
      let element: ASTElement = createASTElement(tag, attrs, currentParent);
      if (ns) {
        element.ns = ns;
      }

      if (process.env.NODE_ENV !== "production") {
        if (options.outputSourceRange) {
          element.start = start;
          element.end = end;
          element.rawAttrsMap = element.attrsList.reduce((cumulated, attr) => {
            cumulated[attr.name] = attr;
            return cumulated;
          }, {});
        }
        attrs.forEach((attr) => {
          // 无效的属性
          if (invalidAttributeRE.test(attr.name)) {
            warn(
              `Invalid dynamic argument expression: attribute names cannot contain ` +
                `spaces, quotes, <, >, / or =.`,
              {
                start: attr.start + attr.name.indexOf(`[`),
                end: attr.start + attr.name.length,
              }
            );
          }
        });
      }

      // 对于script和style标签不解析内容，作出警告
      if (isForbiddenTag(element) && !isServerRendering()) {
        element.forbidden = true;
        process.env.NODE_ENV !== "production" &&
          warn(
            "Templates should only be responsible for mapping the state to the " +
              "UI. Avoid placing tags with side-effects in your templates, such as " +
              `<${tag}>` +
              ", as they will not be parsed.",
            { start: element.start }
          );
      }

      // apply pre-transforms  打印出来好像是处理v-module的
      for (let i = 0; i < preTransforms.length; i++) {
        // 对语法树节点进行预变换？？
        element = preTransforms[i](element, options) || element;
      }

      // 一开始为false   就会执行
      if (!inVPre) {
        // 当前语法树节点解析到了v-pre属性 去除该属性，标记节点对象的pre属性为true
        processPre(element);
        if (element.pre) {
          // 标记当前节点已经是一个v-pre节点
          // v-pre的作用不自动解析vue的插值语法{{}} 最终结果中原样显示
          // 并且也不会解析 ref 得到的语法树节点的children也和普通的语法树节点不同
          inVPre = true;
        }
      }
      //  平台相关函数  pre标签这种？？
      if (platformIsPreTag(element.tag)) {
        inPre = true;
      }

      // 如果是一个 v-pre 节点
      if (inVPre) {
        processRawAttrs(element);
        // 没有processed属性   这个属性是什么添加的？？
        // 这个节点没有处理过   依次执行处理？？
      } else if (!element.processed) {
        // structural directives
        // 解析移除并合并v-for属性的值到语法树节点中
        processFor(element);
        // v-if 还处理了v-else 。。。
        processIf(element);
        // 标记 once 为 true
        processOnce(element);
      }

      if (!root) {
        root = element;
        if (process.env.NODE_ENV !== "production") {
          // 检测root节点  不能是  slot  template  v-for
          checkRootConstraints(root);
        }
      }

      // 不是单标签
      if (!unary) {
        currentParent = element;
        // 放入当前栈中
        stack.push(element);
      } else {
        // 是单标签  运行闭合
        closeElement(element);
      }
    },

    end(tag, start, end) {
      const element = stack[stack.length - 1];
      // pop stack
      stack.length -= 1;
      currentParent = stack[stack.length - 1];
      if (process.env.NODE_ENV !== "production" && options.outputSourceRange) {
        element.end = end;
      }
      closeElement(element);
    },

    // 解析模板中的插值语法  生成一个语法树节点push到父节点的children中
    chars(text: string, start: number, end: number) {
      if (!currentParent) {
        if (process.env.NODE_ENV !== "production") {
          if (text === template) {
            warnOnce(
              "Component template requires a root element, rather than just text.",
              { start }
            );
          } else if ((text = text.trim())) {
            warnOnce(`text "${text}" outside root element will be ignored.`, {
              start,
            });
          }
        }
        return;
      }
      // IE textarea placeholder bug
      /* istanbul ignore if */
      if (
        isIE &&
        currentParent.tag === "textarea" &&
        currentParent.attrsMap.placeholder === text
      ) {
        return;
      }
      const children = currentParent.children;
      if (inPre || text.trim()) {
        // 使用的dom的textContent进行decode
        text = isTextTag(currentParent) ? text : decodeHTMLCached(text);
      } else if (!children.length) {
        // remove the whitespace-only node right after an opening tag
        text = "";
      } else if (whitespaceOption) {
        if (whitespaceOption === "condense") {
          // in condense mode, remove the whitespace node if it contains
          // line break, otherwise condense to a single space
          text = lineBreakRE.test(text) ? "" : " ";
        } else {
          text = " ";
        }
      } else {
        text = preserveWhitespace ? " " : "";
      }
      if (text) {
        if (!inPre && whitespaceOption === "condense") {
          // condense consecutive whitespaces into single space
          text = text.replace(whitespaceRE, " ");
        }
        let res;
        let child: ?ASTNode;
        /*
        input: 测试输出 {{ test }}
        output: {
                expression: "\"测试输出 \"+_s(test)+\" \""
                tokens: [
                  "测试输出 ",
                  {@binding: 'test'},
                  " "
                ]
        }
        */
        if (!inVPre && text !== " " && (res = parseText(text, delimiters))) {
          child = {
            type: 2,
            expression: res.expression,
            tokens: res.tokens,
            text,
          };
        } else if (
          text !== " " ||
          !children.length ||
          children[children.length - 1].text !== " "
        ) {
          child = {
            type: 3,
            text,
          };
        }
        if (child) {
          if (
            process.env.NODE_ENV !== "production" &&
            options.outputSourceRange
          ) {
            child.start = start;
            child.end = end;
          }
          children.push(child);
        }
      }
    },
    comment(text: string, start, end) {
      // adding anything as a sibling to the root node is forbidden
      // comments should still be allowed, but ignored
      if (currentParent) {
        const child: ASTText = {
          type: 3,
          text,
          isComment: true,
        };
        if (
          process.env.NODE_ENV !== "production" &&
          options.outputSourceRange
        ) {
          child.start = start;
          child.end = end;
        }
        currentParent.children.push(child);
      }
    },
  });
  return root;
}

function processPre(el) {
  if (getAndRemoveAttr(el, "v-pre") != null) {
    el.pre = true;
  }
}

function processRawAttrs(el) {
  // 一个数组, 类似于 [{key: 'color', value: 'red'}]  每一项可能还有start，end的索引
  // 基本上等于原样返回，这个好像没必要  之前得到数据是通过正则匹配得来的？？？
  const list = el.attrsList;
  const len = list.length;
  if (len) {
    const attrs: Array<ASTAttr> = (el.attrs = new Array(len));
    for (let i = 0; i < len; i++) {
      attrs[i] = {
        name: list[i].name,
        value: JSON.stringify(list[i].value),
      };
      if (list[i].start != null) {
        attrs[i].start = list[i].start;
        attrs[i].end = list[i].end;
      }
    }
  } else if (!el.pre) {
    // non root node in pre blocks with no attributes
    // 没有属性的节点  标记这个语法树节点的plain属性
    el.plain = true;
  }
}

export function processElement(element: ASTElement, options: CompilerOptions) {
  // 处理key属性  挂载到语法树节点上
  processKey(element);

  // determine whether this is a plain element after
  // removing structural attributes
  // 判断  。。。
  element.plain =
    !element.key && !element.scopedSlots && !element.attrsList.length;

  // 解析出来的ref动态绑定判断  绑定到语法树节点上  规则  如果是动态绑定的ref就是name  如果是普通字符串就是"name"
  // 同时检测是否是一个v-for节点  绑定属性到语法树节点上
  processRef(element);
  // 处理v-slot
  processSlotContent(element);
  // 处理<slot>  slot上还包含 动态的属性绑定  这个暂时没有特殊逻辑处理
  processSlotOutlet(element);
  // 处理 <component is='name'>
  processComponent(element);
  // 一系列方法转换语法树节点。。。   style  class 属性的处理位置
  for (let i = 0; i < transforms.length; i++) {
    element = transforms[i](element, options) || element;
  }
  // 处理语法树节点的attrsList属性   对应parse的attrs属性
  processAttrs(element);
  return element;
}

function processKey(el) {
  // 对于动态绑定的属性，自动解析filter值返回，对于普通属性，直接返回对应的值
  const exp = getBindingAttr(el, "key");
  if (exp) {
    if (process.env.NODE_ENV !== "production") {
      if (el.tag === "template") {
        warn(
          `<template> cannot be keyed. Place the key on real elements instead.`,
          getRawBindingAttr(el, "key")
        );
      }
      // v-for v-if v-pre v-once  优先解析的
      if (el.for) {
        const iterator = el.iterator2 || el.iterator1;
        const parent = el.parent;
        if (
          iterator &&
          iterator === exp &&
          parent &&
          parent.tag === "transition-group"
        ) {
          // 不要使用for的index作为transition-group子组件的key值
          warn(
            `Do not use v-for index as key on <transition-group> children, ` +
              `this is the same as not using keys.`,
            getRawBindingAttr(el, "key"),
            true /* tip */
          );
        }
      }
    }
    // 绑定转换后的key值到语法树节点上
    el.key = exp;
  }
}

function processRef(el) {
  const ref = getBindingAttr(el, "ref");
  if (ref) {
    el.ref = ref;
    el.refInFor = checkInFor(el);
  }
}

export function processFor(el: ASTElement) {
  let exp;
  // 从解析到的v-for属性中得到对应的值 如 {content} in list
  if ((exp = getAndRemoveAttr(el, "v-for"))) {
    const res = parseFor(exp);
    // 返回一个对象 {for: xx, alias: xx, iterator1: xx, iterator2: xx}
    if (res) {
      // 把res中的属性转移到语法树节点上来
      extend(el, res);
    } else if (process.env.NODE_ENV !== "production") {
      // getAndRemoveAttr  不会去除rawAttrsMap中的值
      warn(`Invalid v-for expression: ${exp}`, el.rawAttrsMap["v-for"]);
    }
  }
}

type ForParseResult = {
  for: string,
  alias: string,
  iterator1?: string,
  iterator2?: string,
};

export function parseFor(exp: string): ?ForParseResult {
  const inMatch = exp.match(forAliasRE);
  if (!inMatch) return;
  const res = {};
  res.for = inMatch[2].trim();
  // 去掉括号
  const alias = inMatch[1].trim().replace(stripParensRE, "");
  // 匹配(item, index) in arr 这种情况
  const iteratorMatch = alias.match(forIteratorRE);
  if (iteratorMatch) {
    res.alias = alias.replace(forIteratorRE, "").trim();
    res.iterator1 = iteratorMatch[1].trim();
    if (iteratorMatch[2]) {
      // 对应到循环中的第三个参数  循环体本身
      res.iterator2 = iteratorMatch[2].trim();
    }
  } else {
    // 单个循环元素 item in arr 这种情况
    res.alias = alias;
  }
  return res;
}

function processIf(el) {
  const exp = getAndRemoveAttr(el, "v-if");
  if (exp) {
    el.if = exp;
    // 在语法树节点上创建一个ifConditions属性数组，把传入的对象push到数组中
    addIfCondition(el, {
      exp: exp,
      block: el,
    });
  } else {
    // 从打印的结果上看，这些节点都会push到v-if节点的ifConditions数组中
    if (getAndRemoveAttr(el, "v-else") != null) {
      el.else = true;
    }
    const elseif = getAndRemoveAttr(el, "v-else-if");
    if (elseif) {
      el.elseif = elseif;
    }
  }
}

function processIfConditions(el, parent) {
  const prev = findPrevElement(parent.children);
  if (prev && prev.if) {
    addIfCondition(prev, {
      exp: el.elseif,
      block: el,
    });
  } else if (process.env.NODE_ENV !== "production") {
    warn(
      `v-${el.elseif ? 'else-if="' + el.elseif + '"' : "else"} ` +
        `used on element <${el.tag}> without corresponding v-if.`,
      el.rawAttrsMap[el.elseif ? "v-else-if" : "v-else"]
    );
  }
}

function findPrevElement(children: Array<any>): ASTElement | void {
  let i = children.length;
  while (i--) {
    if (children[i].type === 1) {
      return children[i];
    } else {
      if (process.env.NODE_ENV !== "production" && children[i].text !== " ") {
        warn(
          `text "${children[i].text.trim()}" between v-if and v-else(-if) ` +
            `will be ignored.`,
          children[i]
        );
      }
      children.pop();
    }
  }
}

export function addIfCondition(el: ASTElement, condition: ASTIfCondition) {
  if (!el.ifConditions) {
    el.ifConditions = [];
  }
  el.ifConditions.push(condition);
}

function processOnce(el) {
  const once = getAndRemoveAttr(el, "v-once");
  if (once != null) {
    el.once = true;
  }
}

// 处理传递给插槽的内容 包含作用域插槽
// 作用： 指定插槽名用于渲染  已经传递给当前插槽的数据
// handle content being passed to a component as slot,
// e.g. <template slot="xxx">, <div slot-scope="xxx">
function processSlotContent(el) {
  let slotScope;
  if (el.tag === "template") {
    // scope 不能绑定  只能用在template组件上
    slotScope = getAndRemoveAttr(el, "scope");
    /* istanbul ignore if */
    if (process.env.NODE_ENV !== "production" && slotScope) {
      warn(
        `the "scope" attribute for scoped slots have been deprecated and ` +
          `replaced by "slot-scope" since 2.5. The new "slot-scope" attribute ` +
          `can also be used on plain elements in addition to <template> to ` +
          `denote scoped slots.`,
        el.rawAttrsMap["scope"],
        true
      );
    }
    el.slotScope = slotScope || getAndRemoveAttr(el, "slot-scope");
  } else if ((slotScope = getAndRemoveAttr(el, "slot-scope"))) {
    /* istanbul ignore if */
    if (process.env.NODE_ENV !== "production" && el.attrsMap["v-for"]) {
      warn(
        `Ambiguous combined usage of slot-scope and v-for on <${el.tag}> ` +
          `(v-for takes higher priority). Use a wrapper <template> for the ` +
          `scoped slot to make it clearer.`,
        el.rawAttrsMap["slot-scope"],
        true
      );
    }
    el.slotScope = slotScope;
  }
  // 填充el.slotScope 属性

  // slot="xxx"
  const slotTarget = getBindingAttr(el, "slot");
  if (slotTarget) {
    el.slotTarget = slotTarget === '""' ? '"default"' : slotTarget;
    el.slotTargetDynamic = !!(
      el.attrsMap[":slot"] || el.attrsMap["v-bind:slot"]
    );
    // preserve slot as an attribute for native shadow DOM compat
    // only for non-scoped slots.
    if (el.tag !== "template" && !el.slotScope) {
      addAttr(el, "slot", slotTarget, getRawBindingAttr(el, "slot"));
    }
  }

  // 2.6 v-slot syntax
  // 通过环境变量打开？  神奇
  if (process.env.NEW_SLOT_SYNTAX) {
    if (el.tag === "template") {
      // v-slot on <template>
      // 从语法树的attrs数组中移除 v-slot 属性 并返回
      const slotBinding = getAndRemoveAttrByRegex(el, slotRE);
      if (slotBinding) {
        // 前面的解析已经有了  说明语法问题
        if (process.env.NODE_ENV !== "production") {
          if (el.slotTarget || el.slotScope) {
            // slot语法混合报错
            warn(`Unexpected mixed usage of different slot syntaxes.`, el);
          }
          if (el.parent && !maybeComponent(el.parent)) {
            // 如果slot的父元素是component组件 报错？
            warn(
              `<template v-slot> can only appear at the root level inside ` +
                `the receiving component`,
              el
            );
          }
        }
        const { name, dynamic } = getSlotName(slotBinding);
        // v-slot:[name]='{test}'
        el.slotTarget = name; // name
        el.slotTargetDynamic = dynamic; // true
        // 使用作用域插槽对应的值 类似于{test} 解构取值或者直接取值
        el.slotScope = slotBinding.value || emptySlotScopeToken; // force it into a scoped slot for perf
      }
    } else {
      // v-slot on component, denotes default slot  <component v-slot> </component>  这种用法，，，
      const slotBinding = getAndRemoveAttrByRegex(el, slotRE);
      if (slotBinding) {
        if (process.env.NODE_ENV !== "production") {
          if (!maybeComponent(el)) {
            warn(
              `v-slot can only be used on components or <template>.`,
              slotBinding
            );
          }
          if (el.slotScope || el.slotTarget) {
            warn(`Unexpected mixed usage of different slot syntaxes.`, el);
          }
          if (el.scopedSlots) {
            warn(
              `To avoid scope ambiguity, the default slot should also use ` +
                `<template> syntax when there are other named slots.`,
              slotBinding
            );
          }
        }
        // add the component's children to its default slot
        const slots = el.scopedSlots || (el.scopedSlots = {});
        const { name, dynamic } = getSlotName(slotBinding);
        // 动态创建一个template节点 附加到语法树节点中
        const slotContainer = (slots[name] = createASTElement(
          "template",
          [],
          el
        ));
        slotContainer.slotTarget = name;
        slotContainer.slotTargetDynamic = dynamic;
        // 插槽嵌套。。。
        slotContainer.children = el.children.filter((c: any) => {
          if (!c.slotScope) {
            c.parent = slotContainer;
            return true;
          }
        });
        slotContainer.slotScope = slotBinding.value || emptySlotScopeToken;
        // remove children as they are returned from scopedSlots now
        el.children = [];
        // mark el non-plain so data gets generated
        el.plain = false;
      }
    }
  }
}

function getSlotName(binding) {
  let name = binding.name.replace(slotRE, "");
  if (!name) {
    if (binding.name[0] !== "#") {
      // 默认slot名字
      name = "default";
    } else if (process.env.NODE_ENV !== "production") {
      warn(`v-slot shorthand syntax requires a slot name.`, binding);
    }
  }
  // 解析动态slot名字 [name]
  return dynamicArgRE.test(name)
    ? // dynamic [name]
      { name: name.slice(1, -1), dynamic: true }
    : // static name
      { name: `"${name}"`, dynamic: false };
}

// handle <slot/> outlets
function processSlotOutlet(el) {
  if (el.tag === "slot") {
    // 将绑定的name属性挂载到语法树节点上 对于动态绑定 "name" ,常量 "\"name\""
    el.slotName = getBindingAttr(el, "name");
    if (process.env.NODE_ENV !== "production" && el.key) {
      warn(
        `\`key\` does not work on <slot> because slots are abstract outlets ` +
          `and can possibly expand into multiple elements. ` +
          `Use the key on a wrapping element instead.`,
        getRawBindingAttr(el, "key")
      );
    }
  }
}

function processComponent(el) {
  let binding;
  if ((binding = getBindingAttr(el, "is"))) {
    el.component = binding;
  }
  if (getAndRemoveAttr(el, "inline-template") != null) {
    el.inlineTemplate = true;
  }
}

function processAttrs(el) {
  const list = el.attrsList;
  let i, l, name, rawName, value, modifiers, syncGen, isDynamic;
  for (i = 0, l = list.length; i < l; i++) {
    name = rawName = list[i].name;
    value = list[i].value;
    // 匹配 v- @ # : . 开头的属性名 这些都是在vue中有特殊功能的名字
    if (dirRE.test(name)) {
      // mark element as dynamic
      el.hasBindings = true;
      // modifiers
      // attr的属性名中包含.修饰符  类似于  @click.native  这种  @click.stop
      // 除了事件的额外效果  还支持使用绑定直接的dom属性  如text-content  inner-html  等  使用:text-content.prop = ' "cool" '
      // <video .muted="isMuted"></video>
      // 刚好替换了第一个  modifiers 中就只包含后面的修饰符
      modifiers = parseModifiers(name.replace(dirRE, ""));
      // support .foo shorthand syntax for the .prop modifier
      // 支持 <div .innerHTML="someHTML"></div> 这种写法   本地打包的内容好像不包括这一块
      if (process.env.VBIND_PROP_SHORTHAND && propBindRE.test(name)) {
        (modifiers || (modifiers = {})).prop = true;
        name = `.` + name.slice(1).replace(modifierRE, "");
      } else if (modifiers) {
        name = name.replace(modifierRE, "");
        // modifiers: {native: true}  name: @click
        // modifiers: {prop: true} name: text-content
      }
      // 细化属性的开头判断    如果是bind
      if (bindRE.test(name)) {
        // v-bind
        name = name.replace(bindRE, "");
        // bind的value支持filter  "str | parseInt"
        value = parseFilters(value);
        // [] 动态支持  bind的属性名支持动态
        isDynamic = dynamicArgRE.test(name);
        if (isDynamic) {
          // 是动态的去掉 [] 中括号
          name = name.slice(1, -1);
        }
        // bind value 为空警告
        if (
          process.env.NODE_ENV !== "production" &&
          value.trim().length === 0
        ) {
          warn(
            `The value for a v-bind expression cannot be empty. Found in "v-bind:${name}"`
          );
        }
        if (modifiers) {
          // dom 的属性绑定  不是动态才需要进行name转换   动态则就是一个普通的变量名
          if (modifiers.prop && !isDynamic) {
            name = camelize(name);
            if (name === "innerHtml") name = "innerHTML";
          }
          // 命名驼峰化
          if (modifiers.camel && !isDynamic) {
            name = camelize(name);
          }
          // 新语法糖   这个部分暂时先不看
          if (modifiers.sync) {
            syncGen = genAssignmentCode(value, `$event`);
            if (!isDynamic) {
              addHandler(
                el,
                `update:${camelize(name)}`,
                syncGen,
                null,
                false,
                warn,
                list[i]
              );
              if (hyphenate(name) !== camelize(name)) {
                addHandler(
                  el,
                  `update:${hyphenate(name)}`,
                  syncGen,
                  null,
                  false,
                  warn,
                  list[i]
                );
              }
            } else {
              // handler w/ dynamic event name
              addHandler(
                el,
                `"update:"+(${name})`,
                syncGen,
                null,
                false,
                warn,
                list[i],
                true // dynamic
              );
            }
          }
        }
        // dom属性绑定    动态的
        /*
        platformMustUseProp: 
        function (tag, type, attr) {
          return (
            (attr === "value" && acceptValue(tag) && type !== "button") ||
            (attr === "selected" && tag === "option") ||
            (attr === "checked" && tag === "input") ||
            (attr === "muted" && tag === "video")
          );
        };
        */
        if (
          (modifiers && modifiers.prop) ||
          (!el.component && platformMustUseProp(el.tag, el.attrsMap.type, name))
        ) {
          // 添加 name  value 到语法树节点的props属性上   这是一个数组
          addProp(el, name, value, list[i], isDynamic);
        } else {
          // 添加语法树节点的 attrs  或者  dynamicAttrs   是一个数组
          // 语法树节点创建出来的原始属性 attrList  来自于  parser的attrs的正则匹配   attrsRowMap  保留的原始attrs信息
          addAttr(el, name, value, list[i], isDynamic);
        }
      } else if (onRE.test(name)) {
        // v-on @click --> click
        name = name.replace(onRE, "");
        isDynamic = dynamicArgRE.test(name);
        if (isDynamic) {
          name = name.slice(1, -1);
        }
        // 从结果中看是添加到event属性上 _p 函数是执行bind生成 ？？
        addHandler(el, name, value, modifiers, false, warn, list[i], isDynamic);
      } else {
        // 普通的指令   . 自定义指令
        // normal directives
        name = name.replace(dirRE, "");
        // parse arg
        const argMatch = name.match(argRE);
        let arg = argMatch && argMatch[1];
        isDynamic = false;
        if (arg) {
          name = name.slice(0, -(arg.length + 1));
          if (dynamicArgRE.test(arg)) {
            arg = arg.slice(1, -1);
            isDynamic = true;
          }
        }
        addDirective(
          el,
          name,
          rawName,
          value,
          arg,
          isDynamic,
          modifiers,
          list[i]
        );
        if (process.env.NODE_ENV !== "production" && name === "model") {
          checkForAliasModel(el, value);
        }
      }
    } else {
      // 没有包含 style class 在 module 中提前处理了  只会包含一些其他属性  如 data-set
      // literal attribute
      if (process.env.NODE_ENV !== "production") {
        // 解析模板表达式的 {{ v }} 插值
        const res = parseText(value, delimiters);
        if (res) {
          warn(
            `${name}="${value}": ` +
              "Interpolation inside attributes has been removed. " +
              "Use v-bind or the colon shorthand instead. For example, " +
              'instead of <div id="{{ val }}">, use <div :id="val">.',
            list[i]
          );
        }
      }
      // 新加到语法树节点的attrs属性上
      addAttr(el, name, JSON.stringify(value), list[i]);
      // #6887 firefox doesn't update muted state if set via attribute
      // even immediately after element creation
      if (
        !el.component &&
        name === "muted" &&
        platformMustUseProp(el.tag, el.attrsMap.type, name)
      ) {
        addProp(el, name, "true", list[i]);
      }
    }
  }
}

function checkInFor(el: ASTElement): boolean {
  let parent = el;
  while (parent) {
    if (parent.for !== undefined) {
      return true;
    }
    parent = parent.parent;
  }
  return false;
}

function parseModifiers(name: string): Object | void {
  const match = name.match(modifierRE);
  if (match) {
    const ret = {};
    match.forEach((m) => {
      ret[m.slice(1)] = true;
    });
    return ret;
  }
}

function makeAttrsMap(attrs: Array<Object>): Object {
  const map = {};
  for (let i = 0, l = attrs.length; i < l; i++) {
    if (
      process.env.NODE_ENV !== "production" &&
      map[attrs[i].name] &&
      !isIE &&
      !isEdge
    ) {
      warn("duplicate attribute: " + attrs[i].name, attrs[i]);
    }
    map[attrs[i].name] = attrs[i].value;
  }
  return map;
}

// for script (e.g. type="x/template") or style, do not decode content
function isTextTag(el): boolean {
  return el.tag === "script" || el.tag === "style";
}

function isForbiddenTag(el): boolean {
  return (
    el.tag === "style" ||
    (el.tag === "script" &&
      (!el.attrsMap.type || el.attrsMap.type === "text/javascript"))
  );
}

const ieNSBug = /^xmlns:NS\d+/;
const ieNSPrefix = /^NS\d+:/;

/* istanbul ignore next */
function guardIESVGBug(attrs) {
  const res = [];
  for (let i = 0; i < attrs.length; i++) {
    const attr = attrs[i];
    if (!ieNSBug.test(attr.name)) {
      attr.name = attr.name.replace(ieNSPrefix, "");
      res.push(attr);
    }
  }
  return res;
}

function checkForAliasModel(el, value) {
  let _el = el;
  while (_el) {
    if (_el.for && _el.alias === value) {
      warn(
        `<${el.tag} v-model="${value}">: ` +
          `You are binding v-model directly to a v-for iteration alias. ` +
          `This will not be able to modify the v-for source array because ` +
          `writing to the alias is like modifying a function local variable. ` +
          `Consider using an array of objects and use v-model on an object property instead.`,
        el.rawAttrsMap["v-model"]
      );
    }
    _el = _el.parent;
  }
}
