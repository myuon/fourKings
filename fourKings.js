function jsSetInnerText(elem, context) {
  if (elem.innerText == undefined) { elem.textContent = context; }
  else { elem.innerText = context; }
}

/* Thunk
   Creates a thunk representing the given closure.
   Since we want automatic memoization of as many expressions as possible, we
   use a JS object as a sort of tagged pointer, where the member x denotes the
   object actually pointed to. If a "pointer" points to a thunk, it has a
   member 't' which is set to true; if it points to a value, be it a function,
   a value of an algebraic type of a primitive value, it has no member 't'.
*/

function T(f) {
    this.f = new F(f);
}

function F(f) {
    this.f = f;
}

/* Apply
   Applies the function f to the arguments args. If the application is under-
   saturated, a closure is returned, awaiting further arguments. If it is over-
   saturated, the function is fully applied, and the result (assumed to be a
   function) is then applied to the remaining arguments.
*/
function A(f, args) {
    if(f instanceof T) {
        f = E(f);
    }
    // Closure does some funny stuff with functions that occasionally
    // results in non-functions getting applied, so we have to deal with
    // it.
    if(f.apply === undefined) {
        return f;
    }

    if(f.arity === undefined) {
        f.arity = f.length;
    }
    if(args.length === f.arity) {
        return f.arity === 1 ? f(args[0]) : f.apply(null, args);
    } else if(args.length > f.arity) {
        return f.arity === 1 ? A(f(args.shift()), args)
                             : A(f.apply(null, args.splice(0, f.arity)), args);
    } else {
        var g = function() {
            return A(f, args.concat(Array.prototype.slice.call(arguments)));
        };
        g.arity = f.arity - args.length;
        return g;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f instanceof F) {
            return t.f = t.f.f();
        } else {
            return t.f;
        }
    } else {
        return t;
    }
}

/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw err;
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
function imul(a, b) {
  // ignore high a * high a as the result will always be truncated
  var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
  var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
  var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
  return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function err(str) {
    die(toJSStr(str)[1]);
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = A(f, [[0, str.charCodeAt(i)], acc]);
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,[0,str.charCodeAt(i)],new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1])[1]);
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = A(f, [mv.x]);
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['b']['i8'] = 'U'.charCodeAt(0);
    le['b']['i8'] = 'T'.charCodeAt(0);
    le['b']['i8'] = 'F'.charCodeAt(0);
    le['b']['i8'] = '-'.charCodeAt(0);
    le['b']['i8'] = '8'.charCodeAt(0);
    return le;
}

var isFloatNaN = isDoubleNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return [0];
    } else if(a == b) {
        return [1];
    }
    return [2];
}

function jsCatch(act, handler) {
    try {
        return A(act,[0]);
    } catch(e) {
        return A(handler,[e, 0]);
    }
}

var coercionToken = undefined;

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round; // Stupid GHC doesn't like periods in FFI IDs...
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - e.target.offsetLeft, posy - e.target.offsetTop];
}

function jsSetCB(elem, evt, cb) {
    // Count return press in single line text box as a change event.
    if(evt == 'change' && elem.type.toLowerCase() == 'text') {
        setCB(elem, 'keyup', function(k) {
            if(k == '\n'.charCodeAt(0)) {
                A(cb,[[0,k.keyCode],0]);
            }
        });
    }

    var fun;
    switch(evt) {
    case 'click':
    case 'dblclick':
    case 'mouseup':
    case 'mousedown':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            A(cb,[[0,x.button],[0,mx,my],0]);
        };
        break;
    case 'mousemove':
    case 'mouseover':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            A(cb,[[0,mx,my],0]);
        };
        break;
    case 'keypress':
    case 'keyup':
    case 'keydown':
        fun = function(x) {A(cb,[[0,x.keyCode],0]);};
        break;        
    default:
        fun = function() {A(cb,[0]);};
        break;
    }
    return setCB(elem, evt, fun);
}

function setCB(elem, evt, cb) {
    if(elem.addEventListener) {
        elem.addEventListener(evt, cb, false);
        return true;
    } else if(elem.attachEvent) {
        elem.attachEvent('on'+evt, cb);
        return true;
    }
    return false;
}

function jsSetTimeout(msecs, cb) {
    window.setTimeout(function() {A(cb,[0]);}, msecs);
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    return elem.getAttribute(prop).toString();
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,[0,e]];
    }
    return [0];
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,[0,elem]];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}

function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, [0,elem.childNodes[i]], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(E(children[1])[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1])[1]);
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// Escape all double quotes in a string
function jsUnquote(str) {
    return str.replace(/"/g, '\\"');
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, [0, jsRead(obj)]];
    case 'string':
        return [1, [0, obj]];
        break;
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
        break;
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst(obj, 0)];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, [0,ks[i]], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst(arr,elem+1);})]
}

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);
    xhr.setRequestHeader('Cache-control', 'no-cache');
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                A(cb,[[1,[0,xhr.responseText]],0]);
            } else {
                A(cb,[[0],0]); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;

function makeStableName(x) {
    if(!x.stableName) {
        x.stableName = __next_stable_name;
        __next_stable_name += 1;
    }
    return x.stableName;
}

function eqStableName(x, y) {
    return (x == y) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation; used under the BSD license.

function md5cycle(x, k) {
var a = x[0], b = x[1], c = x[2], d = x[3];

a = ff(a, b, c, d, k[0], 7, -680876936);
d = ff(d, a, b, c, k[1], 12, -389564586);
c = ff(c, d, a, b, k[2], 17,  606105819);
b = ff(b, c, d, a, k[3], 22, -1044525330);
a = ff(a, b, c, d, k[4], 7, -176418897);
d = ff(d, a, b, c, k[5], 12,  1200080426);
c = ff(c, d, a, b, k[6], 17, -1473231341);
b = ff(b, c, d, a, k[7], 22, -45705983);
a = ff(a, b, c, d, k[8], 7,  1770035416);
d = ff(d, a, b, c, k[9], 12, -1958414417);
c = ff(c, d, a, b, k[10], 17, -42063);
b = ff(b, c, d, a, k[11], 22, -1990404162);
a = ff(a, b, c, d, k[12], 7,  1804603682);
d = ff(d, a, b, c, k[13], 12, -40341101);
c = ff(c, d, a, b, k[14], 17, -1502002290);
b = ff(b, c, d, a, k[15], 22,  1236535329);

a = gg(a, b, c, d, k[1], 5, -165796510);
d = gg(d, a, b, c, k[6], 9, -1069501632);
c = gg(c, d, a, b, k[11], 14,  643717713);
b = gg(b, c, d, a, k[0], 20, -373897302);
a = gg(a, b, c, d, k[5], 5, -701558691);
d = gg(d, a, b, c, k[10], 9,  38016083);
c = gg(c, d, a, b, k[15], 14, -660478335);
b = gg(b, c, d, a, k[4], 20, -405537848);
a = gg(a, b, c, d, k[9], 5,  568446438);
d = gg(d, a, b, c, k[14], 9, -1019803690);
c = gg(c, d, a, b, k[3], 14, -187363961);
b = gg(b, c, d, a, k[8], 20,  1163531501);
a = gg(a, b, c, d, k[13], 5, -1444681467);
d = gg(d, a, b, c, k[2], 9, -51403784);
c = gg(c, d, a, b, k[7], 14,  1735328473);
b = gg(b, c, d, a, k[12], 20, -1926607734);

a = hh(a, b, c, d, k[5], 4, -378558);
d = hh(d, a, b, c, k[8], 11, -2022574463);
c = hh(c, d, a, b, k[11], 16,  1839030562);
b = hh(b, c, d, a, k[14], 23, -35309556);
a = hh(a, b, c, d, k[1], 4, -1530992060);
d = hh(d, a, b, c, k[4], 11,  1272893353);
c = hh(c, d, a, b, k[7], 16, -155497632);
b = hh(b, c, d, a, k[10], 23, -1094730640);
a = hh(a, b, c, d, k[13], 4,  681279174);
d = hh(d, a, b, c, k[0], 11, -358537222);
c = hh(c, d, a, b, k[3], 16, -722521979);
b = hh(b, c, d, a, k[6], 23,  76029189);
a = hh(a, b, c, d, k[9], 4, -640364487);
d = hh(d, a, b, c, k[12], 11, -421815835);
c = hh(c, d, a, b, k[15], 16,  530742520);
b = hh(b, c, d, a, k[2], 23, -995338651);

a = ii(a, b, c, d, k[0], 6, -198630844);
d = ii(d, a, b, c, k[7], 10,  1126891415);
c = ii(c, d, a, b, k[14], 15, -1416354905);
b = ii(b, c, d, a, k[5], 21, -57434055);
a = ii(a, b, c, d, k[12], 6,  1700485571);
d = ii(d, a, b, c, k[3], 10, -1894986606);
c = ii(c, d, a, b, k[10], 15, -1051523);
b = ii(b, c, d, a, k[1], 21, -2054922799);
a = ii(a, b, c, d, k[8], 6,  1873313359);
d = ii(d, a, b, c, k[15], 10, -30611744);
c = ii(c, d, a, b, k[6], 15, -1560198380);
b = ii(b, c, d, a, k[13], 21,  1309151649);
a = ii(a, b, c, d, k[4], 6, -145523070);
d = ii(d, a, b, c, k[11], 10, -1120210379);
c = ii(c, d, a, b, k[2], 15,  718787259);
b = ii(b, c, d, a, k[9], 21, -343485551);

x[0] = add32(a, x[0]);
x[1] = add32(b, x[1]);
x[2] = add32(c, x[2]);
x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
a = add32(add32(a, q), add32(x, t));
return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s) {
txt = '';
var n = s.length,
state = [1732584193, -271733879, -1732584194, 271733878], i;
for (i=64; i<=s.length; i+=64) {
md5cycle(state, md5blk(s.substring(i-64, i)));
}
s = s.substring(i-64);
var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
for (i=0; i<s.length; i++)
tail[i>>2] |= s.charCodeAt(i) << ((i%4) << 3);
tail[i>>2] |= 0x80 << ((i%4) << 3);
if (i > 55) {
md5cycle(state, tail);
for (i=0; i<16; i++) tail[i] = 0;
}
tail[14] = n*8;
md5cycle(state, tail);
return state;
}

function md5blk(s) {
var md5blks = [], i;
for (i=0; i<64; i+=4) {
md5blks[i>>2] = s.charCodeAt(i)
+ (s.charCodeAt(i+1) << 8)
+ (s.charCodeAt(i+2) << 16)
+ (s.charCodeAt(i+3) << 24);
}
return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
var s='', j=0;
for(; j<4; j++)
s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
+ hex_chr[(n >> (j * 8)) & 0x0F];
return s;
}

function hex(x) {
for (var i=0; i<x.length; i++)
x[i] = rhex(x[i]);
return x.join('');
}

function md5(s) {
return hex(md51(s));
}

function add32(a, b) {
return (a + b) & 0xFFFFFFFF;
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = [];
    for(; n >= 0; --n) {
        arr.push(x);
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

var _0=[0,0],_1=[0],_2=[0,_1,_1,_1],_3=[1,_2,_1],_4=[1,_2,_3],_5=[1,_2,_4],_6=[1,_2,_5],_7=[0],_8=function(_9,_a){var _b=E(_9);switch(_b[0]){case 0:return [1,_a];case 1:var _c=_b[1],_d=function(_e){var _f=E(_a);return _f[0]==0?[2,_e+_f[1]|0,E([0,_c]),_7,E([0,_f])]:[2,_e+_f[1]|0,E([0,_c]),_7,E([0,_f])];},_g=E(_c);return _g[0]==0?_d(_g[1]):_d(_g[1]);default:var _h=_b[1],_i=_b[2],_j=_b[3],_k=E(_b[4]);switch(_k[0]){case 0:var _l=_k[1],_m=E(_a);return _m[0]==0?[2,_h+_m[1]|0,E(_i),_j,E([1,_l,_m])]:[2,_h+_m[1]|0,E(_i),_j,E([1,_l,_m])];case 1:var _n=_k[1],_o=_k[2],_p=E(_a);return _p[0]==0?[2,_h+_p[1]|0,E(_i),_j,E([2,_n,_o,_p])]:[2,_h+_p[1]|0,E(_i),_j,E([2,_n,_o,_p])];case 2:var _q=_k[1],_r=_k[2],_s=_k[3],_t=E(_a);return _t[0]==0?[2,_h+_t[1]|0,E(_i),_j,E([3,_q,_r,_s,_t])]:[2,_h+_t[1]|0,E(_i),_j,E([3,_q,_r,_s,_t])];default:var _u=_k[1],_v=_k[3],_w=function(_x){return [2,_h+_x|0,E(_i),new T(function(){return _8(E(_j),new T(function(){var _y=function(_z){var _A=E(_k[2]);if(!_A[0]){var _B=_A[1],_C=E(_v);return _C[0]==0?[1,(_z+_B|0)+_C[1]|0,_u,_A,_C]:[1,(_z+_B|0)+_C[1]|0,_u,_A,_C];}else{var _D=_A[1],_E=E(_v);return _E[0]==0?[1,(_z+_D|0)+_E[1]|0,_u,_A,_E]:[1,(_z+_D|0)+_E[1]|0,_u,_A,_E];}},_F=E(_u);return _F[0]==0?_y(_F[1]):_y(_F[1]);}));}),E([1,_k[4],_a])];},_G=E(_a);return _G[0]==0?_w(_G[1]):_w(_G[1]);}}},_H=function(_I,_J){var _K=E(_I);switch(_K[0]){case 0:return [1,_J];case 1:return [2,2,E([0,_K[1]]),_7,E([0,_J])];default:var _L=_K[1],_M=_K[2],_N=_K[3],_O=E(_K[4]);switch(_O[0]){case 0:return [2,_L+1|0,E(_M),_N,E([1,_O[1],_J])];case 1:return [2,_L+1|0,E(_M),_N,E([2,_O[1],_O[2],_J])];case 2:return [2,_L+1|0,E(_M),_N,E([3,_O[1],_O[2],_O[3],_J])];default:return [2,_L+1|0,E(_M),new T(function(){return _8(E(_N),[1,3,_O[1],_O[2],_O[3]]);}),E([1,_O[4],_J])];}}},_P=function(_Q,_R){while(1){var _S=E(_R);if(!_S[0]){return E(_Q);}else{var _T=_H(_Q,_S[1]);_R=_S[2];_Q=_T;continue;}}},_U=new T(function(){return _P(_7,_6);}),_V=[3],_W=function(_X,_Y){var _Z=E(_X);return _Z[0]==0?E(_Y):[1,_Z[1],new T(function(){return _W(_Z[2],_Y);})];},_10=function(_11,_12){var _13=jsShowI(_11);return _W(fromJSStr(_13),_12);},_14=[0,41],_15=[0,40],_16=function(_17,_18,_19){return _18>=0?_10(_18,_19):_17<=6?_10(_18,_19):[1,_15,new T(function(){var _1a=jsShowI(_18);return _W(fromJSStr(_1a),[1,_14,_19]);})];},_1b=[0,41],_1c=[1,_1b,_1],_1d=new T(function(){return _16(0,3,_1c);}),_1e=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",_1d);}),_1f=function(_1g){return err(unAppCStr("toEnum{Suit}: tag (",new T(function(){return _16(0,_1g,_1e);})));},_1h=function(_1i,_1j){if(_1i<=_1j){var _1k=function(_1l){return [1,[0,_1l],new T(function(){return _1l!=_1j?_1k(_1l+1|0):[0];})];};return _1k(_1i);}else{return [0];}},_1m=new T(function(){return _1h(1,13);}),_1n=[1,_0],_1o=[1,_0],_1p=[1,_1o,_1],_1q=[1,_1n,_1p],_1r=function(_1s){var _1t=function(_1u){var _1v=E(_1u);return _1v[0]==0?E(new T(function(){var _1w=E(_1s);return _1w==3?E(_1q):_1r(_1w+1|0);})):[1,[0,new T(function(){return _1s<0?_1f(_1s):_1s>3?_1f(_1s):_1s;}),_1v[1]],new T(function(){return _1t(_1v[2]);})];};return _1t(_1m);},_1x=new T(function(){return _1r(0);}),_1y=[0,_U,_0,_V,_1x,_1,_1,_0,_1,_1],_1z=unCStr("Prelude.(!!): negative index\n"),_1A=new T(function(){return err(_1z);}),_1B=unCStr("Prelude.(!!): index too large\n"),_1C=new T(function(){return err(_1B);}),_1D=function(_1E,_1F){while(1){var _1G=E(_1E);if(!_1G[0]){return E(_1C);}else{var _1H=E(_1F);if(!_1H){return E(_1G[1]);}else{_1E=_1G[2];_1F=_1H-1|0;continue;}}}},_1I=function(_1J,_1K){return E(_1J)[1]==E(_1K)[1];},_1L=function(_1M,_1N){var _1O=new T(function(){switch(E(_1M)[0]){case 0:switch(E(_1N)[0]){case 0:return true;case 1:return false;default:return false;}break;case 1:switch(E(_1N)[0]){case 0:return false;case 1:return true;default:return false;}break;default:switch(E(_1N)[0]){case 0:return false;case 1:return false;default:return true;}}}),_1P=E(_1M);switch(_1P[0]){case 0:var _1Q=_1P[2],_1R=E(_1N);if(!_1R[0]){var _1S=_1R[1],_1T=_1R[2];switch(E(_1P[1])){case 0:switch(E(_1S)){case 0:return _1I(_1Q,_1T);case 1:return false;case 2:return false;default:return false;}break;case 1:return E(_1S)==1?_1I(_1Q,_1T):false;case 2:return E(_1S)==2?_1I(_1Q,_1T):false;default:return E(_1S)==3?_1I(_1Q,_1T):false;}}else{return E(_1O);}break;case 1:var _1U=E(_1N);return _1U[0]==1?_1I(_1P[1],_1U[1]):E(_1O);default:return E(_1O);}},_1V=function(_1W,_1X){return !_1L(_1W,_1X)?true:false;},_1Y=[0,_1L,_1V],_1Z=function(_20){return E(E(_20)[1]);},_21=function(_22,_23,_24){while(1){var _25=E(_23);if(!_25[0]){return E(_24)[0]==0?true:false;}else{var _26=E(_24);if(!_26[0]){return false;}else{if(!A(_1Z,[_22,_25[1],_26[1]])){return false;}else{_23=_25[2];_24=_26[2];continue;}}}}},_27=function(_28,_29,_2a){return !_21(_28,_29,_2a)?true:false;},_2b=function(_2c){return [0,function(_2d,_2e){return _21(_2c,_2d,_2e);},function(_2d,_2e){return _27(_2c,_2d,_2e);}];},_2f=new T(function(){return _2b(_1Y);}),_2g=function(_2h,_2i){var _2j=E(_2i);return _2j[0]==0?[0,_2j[1],new T(function(){return A(_2h,[_2j[2]]);}),new T(function(){return A(_2h,[_2j[3]]);})]:[1,_2j[1],new T(function(){return A(_2h,[_2j[2]]);}),new T(function(){return A(_2h,[_2j[3]]);}),new T(function(){return A(_2h,[_2j[4]]);})];},_2k=function(_2l,_2m){var _2n=E(_2m);switch(_2n[0]){case 0:return [0];case 1:return [1,new T(function(){return A(_2l,[_2n[1]]);})];default:var _2o=_2n[1],_2p=_2n[3],_2q=_2n[4],_2r=E(_2n[2]);switch(_2r[0]){case 0:var _2s=[0,new T(function(){return A(_2l,[_2r[1]]);})];break;case 1:var _2s=[1,new T(function(){return A(_2l,[_2r[1]]);}),new T(function(){return A(_2l,[_2r[2]]);})];break;case 2:var _2s=[2,new T(function(){return A(_2l,[_2r[1]]);}),new T(function(){return A(_2l,[_2r[2]]);}),new T(function(){return A(_2l,[_2r[3]]);})];break;default:var _2s=[3,new T(function(){return A(_2l,[_2r[1]]);}),new T(function(){return A(_2l,[_2r[2]]);}),new T(function(){return A(_2l,[_2r[3]]);}),new T(function(){return A(_2l,[_2r[4]]);})];}var _2t=_2s,_2u=E(_2q);switch(_2u[0]){case 0:var _2v=_2u[1],_2w=new T(function(){return A(_2l,[_2v]);}),_2x=[0,_2w];break;case 1:var _2y=_2u[1],_2z=_2u[2],_2A=new T(function(){return A(_2l,[_2z]);}),_2B=new T(function(){return A(_2l,[_2y]);}),_2x=[1,_2B,_2A];break;case 2:var _2C=_2u[1],_2D=_2u[2],_2E=_2u[3],_2F=new T(function(){return A(_2l,[_2E]);}),_2G=new T(function(){return A(_2l,[_2D]);}),_2H=new T(function(){return A(_2l,[_2C]);}),_2x=[2,_2H,_2G,_2F];break;default:var _2I=_2u[1],_2J=_2u[2],_2K=_2u[3],_2L=_2u[4],_2M=new T(function(){return A(_2l,[_2L]);}),_2N=new T(function(){return A(_2l,[_2K]);}),_2O=new T(function(){return A(_2l,[_2J]);}),_2P=new T(function(){return A(_2l,[_2I]);}),_2x=[3,_2P,_2O,_2N,_2M];}var _2Q=_2x,_2R=new T(function(){return _2k(function(_2S){return _2g(_2l,_2S);},_2p);});return [2,_2o,E(_2t),_2R,E(_2Q)];}},_2T=function(_2U,_2V,_2W){var _2X=E(_2W);return _2X[0]==0?A(_2U,[_2X[2],new T(function(){return A(_2U,[_2X[3],_2V]);})]):A(_2U,[_2X[2],new T(function(){return A(_2U,[_2X[3],new T(function(){return A(_2U,[_2X[4],_2V]);})]);})]);},_2Y=function(_2Z,_30,_31){var _32=E(_31);switch(_32[0]){case 0:return E(_30);case 1:return A(_2Z,[_32[1],_30]);default:var _33=new T(function(){return _2Y(function(_34,_35){return _2T(_2Z,_35,_34);},new T(function(){var _36=E(_32[4]);switch(_36[0]){case 0:return A(_2Z,[_36[1],_30]);case 1:return A(_2Z,[_36[1],new T(function(){return A(_2Z,[_36[2],_30]);})]);case 2:return A(_2Z,[_36[1],new T(function(){return A(_2Z,[_36[2],new T(function(){return A(_2Z,[_36[3],_30]);})]);})]);default:return A(_2Z,[_36[1],new T(function(){return A(_2Z,[_36[2],new T(function(){return A(_2Z,[_36[3],new T(function(){return A(_2Z,[_36[4],_30]);})]);})]);})]);}}),_32[3]);}),_37=E(_32[2]);switch(_37[0]){case 0:return A(_2Z,[_37[1],_33]);case 1:return A(_2Z,[_37[1],new T(function(){return A(_2Z,[_37[2],_33]);})]);case 2:return A(_2Z,[_37[1],new T(function(){return A(_2Z,[_37[2],new T(function(){return A(_2Z,[_37[3],_33]);})]);})]);default:return A(_2Z,[_37[1],new T(function(){return A(_2Z,[_37[2],new T(function(){return A(_2Z,[_37[3],new T(function(){return A(_2Z,[_37[4],_33]);})]);})]);})]);}}},_38=[0,0],_39=function(_3a,_3b){var _3c=new T(function(){switch(E(_3a)[0]){case 0:switch(E(_3b)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:switch(E(_3b)[0]){case 0:return false;case 1:return true;case 2:return false;default:return false;}break;case 2:switch(E(_3b)[0]){case 2:return true;case 3:return false;default:return false;}break;default:switch(E(_3b)[0]){case 2:return false;case 3:return true;default:return false;}}}),_3d=E(_3a);switch(_3d[0]){case 2:var _3e=E(_3b);return _3e[0]==2?_21(_1Y,_3d[1],_3e[1]):E(_3c);case 3:var _3f=E(_3b);return _3f[0]==3?_1L(_3d[1],_3f[1]):E(_3c);default:return E(_3c);}},_3g=function(_3h,_3i){return !_39(_3h,_3i)?true:false;},_3j=[0,_39,_3g],_3k=function(_3l,_3m){return E(_3l)[1]!=E(_3m)[1];},_3n=[0,_1I,_3k],_3o=function(_3p,_3q,_3r){var _3s=E(_3r);return _3s[0]==0?A(_3p,[new T(function(){return A(_3p,[_3q,_3s[2]]);}),_3s[3]]):A(_3p,[new T(function(){return A(_3p,[new T(function(){return A(_3p,[_3q,_3s[2]]);}),_3s[3]]);}),_3s[4]]);},_3t=function(_3u,_3v,_3w){var _3x=E(_3w);switch(_3x[0]){case 0:return E(_3v);case 1:return A(_3u,[_3v,_3x[1]]);default:var _3y=new T(function(){return _3t(function(_3z,_2S){return _3o(_3u,_3z,_2S);},new T(function(){var _3A=E(_3x[2]);switch(_3A[0]){case 0:return A(_3u,[_3v,_3A[1]]);case 1:return A(_3u,[new T(function(){return A(_3u,[_3v,_3A[1]]);}),_3A[2]]);case 2:return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[_3v,_3A[1]]);}),_3A[2]]);}),_3A[3]]);default:return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[_3v,_3A[1]]);}),_3A[2]]);}),_3A[3]]);}),_3A[4]]);}}),_3x[3]);}),_3B=E(_3x[4]);switch(_3B[0]){case 0:return A(_3u,[_3y,_3B[1]]);case 1:return A(_3u,[new T(function(){return A(_3u,[_3y,_3B[1]]);}),_3B[2]]);case 2:return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[_3y,_3B[1]]);}),_3B[2]]);}),_3B[3]]);default:return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[new T(function(){return A(_3u,[_3y,_3B[1]]);}),_3B[2]]);}),_3B[3]]);}),_3B[4]]);}}},_3C=[0,1],_3D=function(_3E,_3F){switch(E(_3E)){case 0:var _3G=E(_3F);return true;case 1:switch(E(_3F)){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 2:switch(E(_3F)){case 2:return true;case 3:return true;default:return false;}break;default:return E(_3F)==3?true:false;}},_3H=[0,5],_3I=[0,6],_3J=[0,7],_3K=[0,8],_3L=[0,9],_3M=[0,10],_3N=[0,11],_3O=[1,_0,_1],_3P=[0,2],_3Q=[1,_3P,_3O],_3R=[1,_3C,_3Q],_3S=[0,13],_3T=[1,_3S,_3R],_3U=[0,12],_3V=[1,_3U,_3T],_3W=[1,_3N,_3V],_3X=[1,_3M,_3W],_3Y=[1,_3L,_3X],_3Z=[1,_3K,_3Y],_40=[1,_3J,_3Z],_41=[1,_3I,_40],_42=[1,_3H,_41],_43=[0,4],_44=[1,_43,_42],_45=[0,3],_46=[1,_45,_44],_47=function(_48,_49){var _4a=function(_4b,_4c){while(1){var _4d=(function(_4e,_4f){var _4g=E(_4f);if(!_4g[0]){return [0];}else{var _4h=_4g[2];if(!A(_48,[_4g[1]])){var _4i=_4e+1|0;_4c=_4h;_4b=_4i;return null;}else{return [1,[0,_4e],new T(function(){return _4a(_4e+1|0,_4h);})];}}})(_4b,_4c);if(_4d!=null){return _4d;}}};return _4a(0,_49);},_4j=unCStr("Maybe.fromJust: Nothing"),_4k=new T(function(){return err(_4j);}),_4l=function(_4m,_4n){var _4o=E(_4n);if(_4o[0]==1){return true;}else{var _4p=E(_4m);switch(_4p[0]){case 0:var _4q=E(_4o);if(!_4q[0]){var _4r=E(_4p[2]),_4s=E(_4q[2]);if(_4r[1]!=_4s[1]){var _4t=_47(function(_4u){return _1I(_4r,_4u);},_46);if(!_4t[0]){return E(_4k);}else{var _4v=_47(function(_4u){return _1I(_4s,_4u);},_46);return _4v[0]==0?E(_4k):E(_4t[1])[1]<=E(_4v[1])[1];}}else{return _3D(_4p[1],_4q[1]);}}else{return true;}break;case 1:return false;default:return true;}}},_4w=function(_4x,_4y){return !_1L(_4x,_4y)?!_4l(_4x,_4y)?2:0:1;},_4z=[0,9830],_4A=[0,75],_4B=[1,_4A,_1],_4C=[1,_4z,_4B],_4D=[0,9829],_4E=[1,_4D,_4B],_4F=[0,9824],_4G=[1,_4F,_4B],_4H=[0,81],_4I=[1,_4H,_1],_4J=[0,9827],_4K=[1,_4J,_4I],_4L=[1,_4z,_4I],_4M=[1,_4D,_4I],_4N=[1,_4F,_4I],_4O=[0,74],_4P=[1,_4O,_1],_4Q=[1,_4J,_4P],_4R=[1,_4z,_4P],_4S=[1,_4D,_4P],_4T=[1,_4F,_4P],_4U=[0,65],_4V=[1,_4U,_1],_4W=[1,_4J,_4V],_4X=[0,65290],_4Y=[1,_4X,_1],_4Z=[1,_4z,_4V],_50=[1,_4D,_4V],_51=[1,_4F,_4V],_52=unCStr("Joker"),_53=[1,_4J,_4B],_54=function(_55){var _56=E(_55);switch(_56[0]){case 0:var _57=_56[1],_58=E(E(_56[2])[1]);switch(_58){case 1:switch(E(_57)){case 0:return E(_51);case 1:return E(_50);case 2:return E(_4Z);default:return E(_4W);}break;case 11:switch(E(_57)){case 0:return E(_4T);case 1:return E(_4S);case 2:return E(_4R);default:return E(_4Q);}break;case 12:switch(E(_57)){case 0:return E(_4N);case 1:return E(_4M);case 2:return E(_4L);default:return E(_4K);}break;case 13:switch(E(_57)){case 0:return E(_4G);case 1:return E(_4E);case 2:return E(_4C);default:return E(_53);}break;default:switch(E(_57)){case 0:return [1,_4F,new T(function(){return _16(0,_58,_1);})];case 1:return [1,_4D,new T(function(){return _16(0,_58,_1);})];case 2:return [1,_4z,new T(function(){return _16(0,_58,_1);})];default:return [1,_4J,new T(function(){return _16(0,_58,_1);})];}}break;case 1:var _59=E(E(_56[1])[1]);return _59==0?E(_52):unAppCStr("Joker ",new T(function(){return _16(0,_59,_1);}));default:return E(_4Y);}},_5a=0,_5b=function(_5c,_5d,_5e,_5f){return A(_5c,[new T(function(){return function(_){var _5g=jsSetAttr(E(_5d)[1],toJSStr(E(_5e)),toJSStr(E(_5f)));return _5a;};})]);},_5h=function(_5i){return E(_5i);},_5j=[0,32],_5k=function(_5l,_5m,_5n,_){var _5o=E(_5m),_5p=jsGetAttr(_5l,toJSStr(_5o));return A(_5b,[_5h,[0,_5l],_5o,new T(function(){return _W(fromJSStr(_5p),[1,_5j,_5n]);}),_]);},_5q=unCStr("adjustTree of empty tree"),_5r=new T(function(){return err(_5q);}),_5s=function(_5t,_5u,_5v){var _5w=E(_5v);switch(_5w[0]){case 0:return E(_5r);case 1:return [1,new T(function(){return A(_5t,[_5u,_5w[1]]);})];default:var _5x=_5w[1],_5y=_5w[2],_5z=_5w[3],_5A=_5w[4],_5B=E(_5u),_5C=_5B[1],_5D=function(_5E){if(_5C>=_5E){var _5F=function(_5G){if(_5C>=_5G){var _5H=_5C-_5G|0,_5I=E(_5A);switch(_5I[0]){case 0:var _5J=[0,new T(function(){return A(_5t,[[0,_5H],_5I[1]]);})];break;case 1:var _5K=_5I[1],_5L=_5I[2],_5M=function(_5N){return _5H>=_5N?[1,_5K,new T(function(){return A(_5t,[[0,_5H-_5N|0],_5L]);})]:[1,new T(function(){return A(_5t,[[0,_5H],_5K]);}),_5L];},_5O=E(_5K),_5J=_5O[0]==0?_5M(_5O[1]):_5M(_5O[1]);break;case 2:var _5P=_5I[1],_5Q=_5I[2],_5R=_5I[3],_5S=function(_5T){if(_5H>=_5T){var _5U=function(_5V){return _5H>=_5V?[2,_5P,_5Q,new T(function(){return A(_5t,[[0,_5H-_5V|0],_5R]);})]:[2,_5P,new T(function(){return A(_5t,[[0,_5H-_5T|0],_5Q]);}),_5R];},_5W=E(_5Q);return _5W[0]==0?_5U(_5T+_5W[1]|0):_5U(_5T+_5W[1]|0);}else{return [2,new T(function(){return A(_5t,[[0,_5H],_5P]);}),_5Q,_5R];}},_5X=E(_5P),_5J=_5X[0]==0?_5S(_5X[1]):_5S(_5X[1]);break;default:var _5Y=_5I[1],_5Z=_5I[2],_60=_5I[3],_61=_5I[4],_62=function(_63){if(_5H>=_63){var _64=function(_65){if(_5H>=_65){var _66=function(_67){return _5H>=_67?[3,_5Y,_5Z,_60,new T(function(){return A(_5t,[[0,_5H-_67|0],_61]);})]:[3,_5Y,_5Z,new T(function(){return A(_5t,[[0,_5H-_65|0],_60]);}),_61];},_68=E(_60);return _68[0]==0?_66(_65+_68[1]|0):_66(_65+_68[1]|0);}else{return [3,_5Y,new T(function(){return A(_5t,[[0,_5H-_63|0],_5Z]);}),_60,_61];}},_69=E(_5Z);return _69[0]==0?_64(_63+_69[1]|0):_64(_63+_69[1]|0);}else{return [3,new T(function(){return A(_5t,[[0,_5H],_5Y]);}),_5Z,_60,_61];}},_6a=E(_5Y),_5J=_6a[0]==0?_62(_6a[1]):_62(_6a[1]);}var _6b=_5J;return [2,_5x,E(_5y),_5z,E(_6b)];}else{return [2,_5x,E(_5y),new T(function(){return _5s(function(_6c,_6d){var _6e=E(_6d);if(!_6e[0]){var _6f=_6e[1],_6g=_6e[2],_6h=_6e[3],_6i=E(_6c),_6j=_6i[1],_6k=function(_6l){return _6j>=_6l?[0,_6f,_6g,new T(function(){return A(_5t,[[0,_6j-_6l|0],_6h]);})]:[0,_6f,new T(function(){return A(_5t,[_6i,_6g]);}),_6h];},_6m=E(_6g);return _6m[0]==0?_6k(_6m[1]):_6k(_6m[1]);}else{var _6n=_6e[1],_6o=_6e[2],_6p=_6e[3],_6q=_6e[4],_6r=E(_6c),_6s=_6r[1],_6t=function(_6u){if(_6s>=_6u){var _6v=function(_6w){return _6s>=_6w?[1,_6n,_6o,_6p,new T(function(){return A(_5t,[[0,_6s-_6w|0],_6q]);})]:[1,_6n,_6o,new T(function(){return A(_5t,[[0,_6s-_6u|0],_6p]);}),_6q];},_6x=E(_6p);return _6x[0]==0?_6v(_6u+_6x[1]|0):_6v(_6u+_6x[1]|0);}else{return [1,_6n,new T(function(){return A(_5t,[_6r,_6o]);}),_6p,_6q];}},_6y=E(_6o);return _6y[0]==0?_6t(_6y[1]):_6t(_6y[1]);}},[0,_5C-_5E|0],_5z);}),E(_5A)];}},_6z=E(_5z);switch(_6z[0]){case 0:return _5F(_5E);case 1:var _6A=E(_6z[1]);return _6A[0]==0?_5F(_5E+_6A[1]|0):_5F(_5E+_6A[1]|0);default:return _5F(_5E+_6z[1]|0);}}else{var _6B=E(_5y);switch(_6B[0]){case 0:var _6C=[0,new T(function(){return A(_5t,[_5B,_6B[1]]);})];break;case 1:var _6D=_6B[1],_6E=_6B[2],_6F=function(_6G){return _5C>=_6G?[1,_6D,new T(function(){return A(_5t,[[0,_5C-_6G|0],_6E]);})]:[1,new T(function(){return A(_5t,[_5B,_6D]);}),_6E];},_6H=E(_6D),_6C=_6H[0]==0?_6F(_6H[1]):_6F(_6H[1]);break;case 2:var _6I=_6B[1],_6J=_6B[2],_6K=_6B[3],_6L=function(_6M){if(_5C>=_6M){var _6N=function(_6O){return _5C>=_6O?[2,_6I,_6J,new T(function(){return A(_5t,[[0,_5C-_6O|0],_6K]);})]:[2,_6I,new T(function(){return A(_5t,[[0,_5C-_6M|0],_6J]);}),_6K];},_6P=E(_6J);return _6P[0]==0?_6N(_6M+_6P[1]|0):_6N(_6M+_6P[1]|0);}else{return [2,new T(function(){return A(_5t,[_5B,_6I]);}),_6J,_6K];}},_6Q=E(_6I),_6C=_6Q[0]==0?_6L(_6Q[1]):_6L(_6Q[1]);break;default:var _6R=_6B[1],_6S=_6B[2],_6T=_6B[3],_6U=_6B[4],_6V=function(_6W){if(_5C>=_6W){var _6X=function(_6Y){if(_5C>=_6Y){var _6Z=function(_70){return _5C>=_70?[3,_6R,_6S,_6T,new T(function(){return A(_5t,[[0,_5C-_70|0],_6U]);})]:[3,_6R,_6S,new T(function(){return A(_5t,[[0,_5C-_6Y|0],_6T]);}),_6U];},_71=E(_6T);return _71[0]==0?_6Z(_6Y+_71[1]|0):_6Z(_6Y+_71[1]|0);}else{return [3,_6R,new T(function(){return A(_5t,[[0,_5C-_6W|0],_6S]);}),_6T,_6U];}},_72=E(_6S);return _72[0]==0?_6X(_6W+_72[1]|0):_6X(_6W+_72[1]|0);}else{return [3,new T(function(){return A(_5t,[_5B,_6R]);}),_6S,_6T,_6U];}},_73=E(_6R),_6C=_73[0]==0?_6V(_73[1]):_6V(_73[1]);}var _74=_6C;return [2,_5x,E(_74),_5z,E(_5A)];}},_75=E(_5y);switch(_75[0]){case 0:var _76=E(_75[1]);return _76[0]==0?_5D(_76[1]):_5D(_76[1]);case 1:var _77=_75[2],_78=E(_75[1]);if(!_78[0]){var _79=_78[1],_7a=E(_77);return _7a[0]==0?_5D(_79+_7a[1]|0):_5D(_79+_7a[1]|0);}else{var _7b=_78[1],_7c=E(_77);return _7c[0]==0?_5D(_7b+_7c[1]|0):_5D(_7b+_7c[1]|0);}break;case 2:var _7d=_75[3],_7e=function(_7f){var _7g=E(_75[2]);if(!_7g[0]){var _7h=_7g[1],_7i=E(_7d);return _7i[0]==0?_5D((_7f+_7h|0)+_7i[1]|0):_5D((_7f+_7h|0)+_7i[1]|0);}else{var _7j=_7g[1],_7k=E(_7d);return _7k[0]==0?_5D((_7f+_7j|0)+_7k[1]|0):_5D((_7f+_7j|0)+_7k[1]|0);}},_7l=E(_75[1]);return _7l[0]==0?_7e(_7l[1]):_7e(_7l[1]);default:var _7m=_75[4],_7n=function(_7o){var _7p=function(_7q){var _7r=E(_75[3]);if(!_7r[0]){var _7s=_7r[1],_7t=E(_7m);return _7t[0]==0?_5D(((_7o+_7q|0)+_7s|0)+_7t[1]|0):_5D(((_7o+_7q|0)+_7s|0)+_7t[1]|0);}else{var _7u=_7r[1],_7v=E(_7m);return _7v[0]==0?_5D(((_7o+_7q|0)+_7u|0)+_7v[1]|0):_5D(((_7o+_7q|0)+_7u|0)+_7v[1]|0);}},_7w=E(_75[2]);return _7w[0]==0?_7p(_7w[1]):_7p(_7w[1]);},_7x=E(_75[1]);return _7x[0]==0?_7n(_7x[1]):_7n(_7x[1]);}}},_7y=new T(function(){return err(_5q);}),_7z=function(_7A,_7B,_7C){if(0>_7B){return E(_7C);}else{var _7D=new T(function(){var _7E=E(_7C);switch(_7E[0]){case 0:return E(_7y);case 1:return [1,new T(function(){return A(_7A,[_7E[1]]);})];default:var _7F=_7E[1],_7G=_7E[2],_7H=_7E[3],_7I=_7E[4],_7J=function(_7K){if(_7B>=_7K){var _7L=function(_7M){if(_7B>=_7M){var _7N=E(_7I);switch(_7N[0]){case 0:var _7O=[0,new T(function(){return A(_7A,[_7N[1]]);})];break;case 1:var _7P=_7N[1],_7Q=_7N[2],_7O=(_7B-_7M|0)>=1?[1,_7P,new T(function(){return A(_7A,[_7Q]);})]:[1,new T(function(){return A(_7A,[_7P]);}),_7Q];break;case 2:var _7R=_7N[1],_7S=_7N[2],_7T=_7N[3],_7U=_7B-_7M|0,_7O=_7U>=1?_7U>=2?[2,_7R,_7S,new T(function(){return A(_7A,[_7T]);})]:[2,_7R,new T(function(){return A(_7A,[_7S]);}),_7T]:[2,new T(function(){return A(_7A,[_7R]);}),_7S,_7T];break;default:var _7V=_7N[1],_7W=_7N[2],_7X=_7N[3],_7Y=_7N[4],_7Z=_7B-_7M|0,_7O=_7Z>=1?_7Z>=2?_7Z>=3?[3,_7V,_7W,_7X,new T(function(){return A(_7A,[_7Y]);})]:[3,_7V,_7W,new T(function(){return A(_7A,[_7X]);}),_7Y]:[3,_7V,new T(function(){return A(_7A,[_7W]);}),_7X,_7Y]:[3,new T(function(){return A(_7A,[_7V]);}),_7W,_7X,_7Y];}var _80=_7O;return [2,_7F,E(_7G),_7H,E(_80)];}else{return [2,_7F,E(_7G),new T(function(){return _5s(function(_81,_82){var _83=E(_82);if(!_83[0]){var _84=_83[1],_85=_83[2],_86=_83[3];return E(_81)[1]>=1?[0,_84,_85,new T(function(){return A(_7A,[_86]);})]:[0,_84,new T(function(){return A(_7A,[_85]);}),_86];}else{var _87=_83[1],_88=_83[2],_89=_83[3],_8a=_83[4],_8b=E(_81)[1];return _8b>=1?_8b>=2?[1,_87,_88,_89,new T(function(){return A(_7A,[_8a]);})]:[1,_87,_88,new T(function(){return A(_7A,[_89]);}),_8a]:[1,_87,new T(function(){return A(_7A,[_88]);}),_89,_8a];}},[0,_7B-_7K|0],_7H);}),E(_7I)];}},_8c=E(_7H);switch(_8c[0]){case 0:return _7L(_7K);case 1:var _8d=E(_8c[1]);return _8d[0]==0?_7L(_7K+_8d[1]|0):_7L(_7K+_8d[1]|0);default:return _7L(_7K+_8c[1]|0);}}else{var _8e=E(_7G);switch(_8e[0]){case 0:var _8f=[0,new T(function(){return A(_7A,[_8e[1]]);})];break;case 1:var _8g=_8e[1],_8h=_8e[2],_8f=_7B>=1?[1,_8g,new T(function(){return A(_7A,[_8h]);})]:[1,new T(function(){return A(_7A,[_8g]);}),_8h];break;case 2:var _8i=_8e[1],_8j=_8e[2],_8k=_8e[3],_8f=_7B>=1?_7B>=2?[2,_8i,_8j,new T(function(){return A(_7A,[_8k]);})]:[2,_8i,new T(function(){return A(_7A,[_8j]);}),_8k]:[2,new T(function(){return A(_7A,[_8i]);}),_8j,_8k];break;default:var _8l=_8e[1],_8m=_8e[2],_8n=_8e[3],_8o=_8e[4],_8f=_7B>=1?_7B>=2?_7B>=3?[3,_8l,_8m,_8n,new T(function(){return A(_7A,[_8o]);})]:[3,_8l,_8m,new T(function(){return A(_7A,[_8n]);}),_8o]:[3,_8l,new T(function(){return A(_7A,[_8m]);}),_8n,_8o]:[3,new T(function(){return A(_7A,[_8l]);}),_8m,_8n,_8o];}var _8p=_8f;return [2,_7F,E(_8p),_7H,E(_7I)];}};switch(E(_7G)[0]){case 0:return _7J(1);case 1:return _7J(2);case 2:return _7J(3);default:return _7J(4);}}}),_8q=E(_7C);switch(_8q[0]){case 0:return _7B>=0?[0]:E(_7D);case 1:return _7B>=1?E(_8q):E(_7D);default:return _7B>=_8q[1]?E(_8q):E(_7D);}}},_8r=function(_8s){var _8t=E(_8s);return _8t[0]==0?[0]:_W(_8t[1],new T(function(){return _8r(_8t[2]);}));},_8u=function(_8v,_8w){var _8x=E(_8w);return _8x[0]==0?[0]:[1,new T(function(){return A(_8v,[_8x[1]]);}),new T(function(){return _8u(_8v,_8x[2]);})];},_8y=function(_8z){return E(E(_8z)[2]);},_8A=unCStr("Prelude.undefined"),_8B=new T(function(){return err(_8A);}),_8C=function(_8D,_){var _8E=rMV(_8D),_=wMV(_8D,new T(function(){var _8F=E(_8E),_8G=_8F[3];return [0,new T(function(){var _8H=E(_8G);return _8H[0]==2?_7z(function(_8I){var _8J=E(_8I);return [0,_8J[1],new T(function(){return _W(new T(function(){return _8r(_8u(_8y,_8F[5]));}),_8J[2]);}),_8J[3]];},E(_8H[1])[1],_8F[1]):E(_8B);}),_8F[2],_8G,_8F[4],_1,_1,_8F[7],_8F[8],_8F[9]];}));return _5a;},_8K=unCStr("lookupTree of empty tree"),_8L=new T(function(){return err(_8K);}),_8M=function(_8N,_8O){var _8P=E(_8O);switch(_8P[0]){case 0:return E(_8L);case 1:return [0,_8N,_8P[1]];default:var _8Q=_8P[2],_8R=_8P[3],_8S=function(_8T){if(_8N>=_8T){var _8U=function(_8V){if(_8N>=_8V){var _8W=_8N-_8V|0,_8X=E(_8P[4]);switch(_8X[0]){case 0:return [0,_8W,_8X[1]];case 1:var _8Y=_8X[2],_8Z=E(_8X[1]);if(!_8Z[0]){var _90=_8Z[1];return _8W>=_90?[0,_8W-_90|0,_8Y]:[0,_8W,_8Z];}else{var _91=_8Z[1];return _8W>=_91?[0,_8W-_91|0,_8Y]:[0,_8W,_8Z];}break;case 2:var _92=_8X[2],_93=_8X[3],_94=E(_8X[1]);if(!_94[0]){var _95=_94[1];if(_8W>=_95){var _96=E(_92);if(!_96[0]){var _97=_95+_96[1]|0;return _8W>=_97?[0,_8W-_97|0,_93]:[0,_8W-_95|0,_96];}else{var _98=_95+_96[1]|0;return _8W>=_98?[0,_8W-_98|0,_93]:[0,_8W-_95|0,_96];}}else{return [0,_8W,_94];}}else{var _99=_94[1];if(_8W>=_99){var _9a=E(_92);if(!_9a[0]){var _9b=_99+_9a[1]|0;return _8W>=_9b?[0,_8W-_9b|0,_93]:[0,_8W-_99|0,_9a];}else{var _9c=_99+_9a[1]|0;return _8W>=_9c?[0,_8W-_9c|0,_93]:[0,_8W-_99|0,_9a];}}else{return [0,_8W,_94];}}break;default:var _9d=_8X[2],_9e=_8X[3],_9f=_8X[4],_9g=E(_8X[1]);if(!_9g[0]){var _9h=_9g[1];if(_8W>=_9h){var _9i=E(_9d);if(!_9i[0]){var _9j=_9h+_9i[1]|0;if(_8W>=_9j){var _9k=E(_9e);if(!_9k[0]){var _9l=_9j+_9k[1]|0;return _8W>=_9l?[0,_8W-_9l|0,_9f]:[0,_8W-_9j|0,_9k];}else{var _9m=_9j+_9k[1]|0;return _8W>=_9m?[0,_8W-_9m|0,_9f]:[0,_8W-_9j|0,_9k];}}else{return [0,_8W-_9h|0,_9i];}}else{var _9n=_9h+_9i[1]|0;if(_8W>=_9n){var _9o=E(_9e);if(!_9o[0]){var _9p=_9n+_9o[1]|0;return _8W>=_9p?[0,_8W-_9p|0,_9f]:[0,_8W-_9n|0,_9o];}else{var _9q=_9n+_9o[1]|0;return _8W>=_9q?[0,_8W-_9q|0,_9f]:[0,_8W-_9n|0,_9o];}}else{return [0,_8W-_9h|0,_9i];}}}else{return [0,_8W,_9g];}}else{var _9r=_9g[1];if(_8W>=_9r){var _9s=E(_9d);if(!_9s[0]){var _9t=_9r+_9s[1]|0;if(_8W>=_9t){var _9u=E(_9e);if(!_9u[0]){var _9v=_9t+_9u[1]|0;return _8W>=_9v?[0,_8W-_9v|0,_9f]:[0,_8W-_9t|0,_9u];}else{var _9w=_9t+_9u[1]|0;return _8W>=_9w?[0,_8W-_9w|0,_9f]:[0,_8W-_9t|0,_9u];}}else{return [0,_8W-_9r|0,_9s];}}else{var _9x=_9r+_9s[1]|0;if(_8W>=_9x){var _9y=E(_9e);if(!_9y[0]){var _9z=_9x+_9y[1]|0;return _8W>=_9z?[0,_8W-_9z|0,_9f]:[0,_8W-_9x|0,_9y];}else{var _9A=_9x+_9y[1]|0;return _8W>=_9A?[0,_8W-_9A|0,_9f]:[0,_8W-_9x|0,_9y];}}else{return [0,_8W-_9r|0,_9s];}}}else{return [0,_8W,_9g];}}}}else{var _9B=_8M(_8N-_8T|0,_8R),_9C=_9B[1],_9D=E(_9B[2]);if(!_9D[0]){var _9E=_9D[3],_9F=E(_9D[2]);if(!_9F[0]){var _9G=_9F[1];return _9C>=_9G?[0,_9C-_9G|0,_9E]:[0,_9C,_9F];}else{var _9H=_9F[1];return _9C>=_9H?[0,_9C-_9H|0,_9E]:[0,_9C,_9F];}}else{var _9I=_9D[3],_9J=_9D[4],_9K=E(_9D[2]);if(!_9K[0]){var _9L=_9K[1];if(_9C>=_9L){var _9M=E(_9I);if(!_9M[0]){var _9N=_9L+_9M[1]|0;return _9C>=_9N?[0,_9C-_9N|0,_9J]:[0,_9C-_9L|0,_9M];}else{var _9O=_9L+_9M[1]|0;return _9C>=_9O?[0,_9C-_9O|0,_9J]:[0,_9C-_9L|0,_9M];}}else{return [0,_9C,_9K];}}else{var _9P=_9K[1];if(_9C>=_9P){var _9Q=E(_9I);if(!_9Q[0]){var _9R=_9P+_9Q[1]|0;return _9C>=_9R?[0,_9C-_9R|0,_9J]:[0,_9C-_9P|0,_9Q];}else{var _9S=_9P+_9Q[1]|0;return _9C>=_9S?[0,_9C-_9S|0,_9J]:[0,_9C-_9P|0,_9Q];}}else{return [0,_9C,_9K];}}}}},_9T=E(_8R);switch(_9T[0]){case 0:return _8U(_8T);case 1:var _9U=E(_9T[1]);return _9U[0]==0?_8U(_8T+_9U[1]|0):_8U(_8T+_9U[1]|0);default:return _8U(_8T+_9T[1]|0);}}else{var _9V=E(_8Q);switch(_9V[0]){case 0:return [0,_8N,_9V[1]];case 1:var _9W=_9V[2],_9X=E(_9V[1]);if(!_9X[0]){var _9Y=_9X[1];return _8N>=_9Y?[0,_8N-_9Y|0,_9W]:[0,_8N,_9X];}else{var _9Z=_9X[1];return _8N>=_9Z?[0,_8N-_9Z|0,_9W]:[0,_8N,_9X];}break;case 2:var _a0=_9V[2],_a1=_9V[3],_a2=E(_9V[1]);if(!_a2[0]){var _a3=_a2[1];if(_8N>=_a3){var _a4=E(_a0);if(!_a4[0]){var _a5=_a3+_a4[1]|0;return _8N>=_a5?[0,_8N-_a5|0,_a1]:[0,_8N-_a3|0,_a4];}else{var _a6=_a3+_a4[1]|0;return _8N>=_a6?[0,_8N-_a6|0,_a1]:[0,_8N-_a3|0,_a4];}}else{return [0,_8N,_a2];}}else{var _a7=_a2[1];if(_8N>=_a7){var _a8=E(_a0);if(!_a8[0]){var _a9=_a7+_a8[1]|0;return _8N>=_a9?[0,_8N-_a9|0,_a1]:[0,_8N-_a7|0,_a8];}else{var _aa=_a7+_a8[1]|0;return _8N>=_aa?[0,_8N-_aa|0,_a1]:[0,_8N-_a7|0,_a8];}}else{return [0,_8N,_a2];}}break;default:var _ab=_9V[2],_ac=_9V[3],_ad=_9V[4],_ae=E(_9V[1]);if(!_ae[0]){var _af=_ae[1];if(_8N>=_af){var _ag=E(_ab);if(!_ag[0]){var _ah=_af+_ag[1]|0;if(_8N>=_ah){var _ai=E(_ac);if(!_ai[0]){var _aj=_ah+_ai[1]|0;return _8N>=_aj?[0,_8N-_aj|0,_ad]:[0,_8N-_ah|0,_ai];}else{var _ak=_ah+_ai[1]|0;return _8N>=_ak?[0,_8N-_ak|0,_ad]:[0,_8N-_ah|0,_ai];}}else{return [0,_8N-_af|0,_ag];}}else{var _al=_af+_ag[1]|0;if(_8N>=_al){var _am=E(_ac);if(!_am[0]){var _an=_al+_am[1]|0;return _8N>=_an?[0,_8N-_an|0,_ad]:[0,_8N-_al|0,_am];}else{var _ao=_al+_am[1]|0;return _8N>=_ao?[0,_8N-_ao|0,_ad]:[0,_8N-_al|0,_am];}}else{return [0,_8N-_af|0,_ag];}}}else{return [0,_8N,_ae];}}else{var _ap=_ae[1];if(_8N>=_ap){var _aq=E(_ab);if(!_aq[0]){var _ar=_ap+_aq[1]|0;if(_8N>=_ar){var _as=E(_ac);if(!_as[0]){var _at=_ar+_as[1]|0;return _8N>=_at?[0,_8N-_at|0,_ad]:[0,_8N-_ar|0,_as];}else{var _au=_ar+_as[1]|0;return _8N>=_au?[0,_8N-_au|0,_ad]:[0,_8N-_ar|0,_as];}}else{return [0,_8N-_ap|0,_aq];}}else{var _av=_ap+_aq[1]|0;if(_8N>=_av){var _aw=E(_ac);if(!_aw[0]){var _ax=_av+_aw[1]|0;return _8N>=_ax?[0,_8N-_ax|0,_ad]:[0,_8N-_av|0,_aw];}else{var _ay=_av+_aw[1]|0;return _8N>=_ay?[0,_8N-_ay|0,_ad]:[0,_8N-_av|0,_aw];}}else{return [0,_8N-_ap|0,_aq];}}}else{return [0,_8N,_ae];}}}}},_az=E(_8Q);switch(_az[0]){case 0:var _aA=E(_az[1]);return _aA[0]==0?_8S(_aA[1]):_8S(_aA[1]);case 1:var _aB=_az[2],_aC=E(_az[1]);if(!_aC[0]){var _aD=_aC[1],_aE=E(_aB);return _aE[0]==0?_8S(_aD+_aE[1]|0):_8S(_aD+_aE[1]|0);}else{var _aF=_aC[1],_aG=E(_aB);return _aG[0]==0?_8S(_aF+_aG[1]|0):_8S(_aF+_aG[1]|0);}break;case 2:var _aH=_az[3],_aI=function(_aJ){var _aK=E(_az[2]);if(!_aK[0]){var _aL=_aK[1],_aM=E(_aH);return _aM[0]==0?_8S((_aJ+_aL|0)+_aM[1]|0):_8S((_aJ+_aL|0)+_aM[1]|0);}else{var _aN=_aK[1],_aO=E(_aH);return _aO[0]==0?_8S((_aJ+_aN|0)+_aO[1]|0):_8S((_aJ+_aN|0)+_aO[1]|0);}},_aP=E(_az[1]);return _aP[0]==0?_aI(_aP[1]):_aI(_aP[1]);default:var _aQ=_az[4],_aR=function(_aS){var _aT=function(_aU){var _aV=E(_az[3]);if(!_aV[0]){var _aW=_aV[1],_aX=E(_aQ);return _aX[0]==0?_8S(((_aS+_aU|0)+_aW|0)+_aX[1]|0):_8S(((_aS+_aU|0)+_aW|0)+_aX[1]|0);}else{var _aY=_aV[1],_aZ=E(_aQ);return _aZ[0]==0?_8S(((_aS+_aU|0)+_aY|0)+_aZ[1]|0):_8S(((_aS+_aU|0)+_aY|0)+_aZ[1]|0);}},_b0=E(_az[2]);return _b0[0]==0?_aT(_b0[1]):_aT(_b0[1]);},_b1=E(_az[1]);return _b1[0]==0?_aR(_b1[1]):_aR(_b1[1]);}}},_b2=unCStr("index out of bounds"),_b3=new T(function(){return err(_b2);}),_b4=new T(function(){return err(_8K);}),_b5=function(_b6,_b7){if(0>_b7){return E(_b3);}else{var _b8=new T(function(){var _b9=E(_b6);switch(_b9[0]){case 0:return E(_b4);case 1:return E(_b9[1]);default:var _ba=_b9[2],_bb=_b9[3],_bc=function(_bd){if(_b7>=_bd){var _be=function(_bf){if(_b7>=_bf){var _bg=E(_b9[4]);switch(_bg[0]){case 0:return E(_bg[1]);case 1:return (_b7-_bf|0)>=1?E(_bg[2]):E(_bg[1]);case 2:var _bh=_b7-_bf|0;return _bh>=1?_bh>=2?E(_bg[3]):E(_bg[2]):E(_bg[1]);default:var _bi=_b7-_bf|0;return _bi>=1?_bi>=2?_bi>=3?E(_bg[4]):E(_bg[3]):E(_bg[2]):E(_bg[1]);}}else{var _bj=_8M(_b7-_bd|0,_bb),_bk=_bj[1],_bl=E(_bj[2]);return _bl[0]==0?_bk>=1?E(_bl[3]):E(_bl[2]):_bk>=1?_bk>=2?E(_bl[4]):E(_bl[3]):E(_bl[2]);}},_bm=E(_bb);switch(_bm[0]){case 0:return _be(_bd);case 1:var _bn=E(_bm[1]);return _bn[0]==0?_be(_bd+_bn[1]|0):_be(_bd+_bn[1]|0);default:return _be(_bd+_bm[1]|0);}}else{var _bo=E(_ba);switch(_bo[0]){case 0:return E(_bo[1]);case 1:return _b7>=1?E(_bo[2]):E(_bo[1]);case 2:return _b7>=1?_b7>=2?E(_bo[3]):E(_bo[2]):E(_bo[1]);default:return _b7>=1?_b7>=2?_b7>=3?E(_bo[4]):E(_bo[3]):E(_bo[2]):E(_bo[1]);}}};switch(E(_ba)[0]){case 0:return _bc(1);case 1:return _bc(2);case 2:return _bc(3);default:return _bc(4);}}}),_bp=E(_b6);switch(_bp[0]){case 0:return _b7>=0?E(_b3):E(_b8);case 1:return _b7>=1?E(_b3):E(_b8);default:return _b7>=_bp[1]?E(_b3):E(_b8);}}},_bq=function(_br,_bs){while(1){var _bt=E(_br);if(!_bt[0]){return E(_bs);}else{_br=_bt[2];var _bu=_bs+1|0;_bs=_bu;continue;}}},_bv=function(_bw,_bx,_by,_bz){return A(_bw,[new T(function(){return function(_){var _bA=jsSet(E(_bx)[1],toJSStr(E(_by)),toJSStr(E(_bz)));return _5a;};})]);},_bB=function(_bC,_bD,_bE,_bF){return A(_bC,[new T(function(){return function(_){var _bG=jsSetStyle(E(_bD)[1],toJSStr(E(_bE)),toJSStr(E(_bF)));return _5a;};})]);},_bH=function(_bI,_bJ){var _bK=E(_bI);if(!_bK){return [0,_1,_bJ];}else{var _bL=E(_bJ);if(!_bL[0]){return [0,_1,_1];}else{var _bM=new T(function(){var _bN=_bH(_bK-1|0,_bL[2]);return [0,_bN[1],_bN[2]];});return [0,[1,_bL[1],new T(function(){return E(E(_bM)[1]);})],new T(function(){return E(E(_bM)[2]);})];}}},_bO=function(_bP,_bQ){while(1){var _bR=E(_bP);if(!_bR[0]){return E(_bQ);}else{_bP=_bR[2];var _bS=_bQ+E(_bR[1])[1]|0;_bQ=_bS;continue;}}},_bT=function(_bU,_bV){var _bW=E(_bU);if(!_bW[0]){var _bX=E(_bV);return _bX[0]==0?_1I(_bW[2],_bX[2]):false;}else{return false;}},_bY=function(_bZ,_c0){var _c1=E(_c0);if(!_c1[0]){return [0,_1,_1];}else{var _c2=_c1[1];if(!A(_bZ,[_c2])){return [0,_1,_c1];}else{var _c3=new T(function(){var _c4=_bY(_bZ,_c1[2]);return [0,_c4[1],_c4[2]];});return [0,[1,_c2,new T(function(){return E(E(_c3)[1]);})],new T(function(){return E(E(_c3)[2]);})];}}},_c5=function(_c6,_c7){var _c8=E(_c7);if(!_c8[0]){return [0];}else{var _c9=_c8[1],_ca=new T(function(){var _cb=_bY(new T(function(){return A(_c6,[_c9]);}),_c8[2]);return [0,_cb[1],_cb[2]];});return [1,[1,_c9,new T(function(){return E(E(_ca)[1]);})],new T(function(){return _c5(_c6,E(_ca)[2]);})];}},_cc=[0,-1],_cd=[1,_1,_1],_ce=function(_cf,_cg){var _ch=function(_ci,_cj){var _ck=E(_ci);if(!_ck[0]){return E(_cj);}else{var _cl=_ck[1],_cm=E(_cj);if(!_cm[0]){return E(_ck);}else{var _cn=_cm[1];return A(_cf,[_cl,_cn])==2?[1,_cn,new T(function(){return _ch(_ck,_cm[2]);})]:[1,_cl,new T(function(){return _ch(_ck[2],_cm);})];}}},_co=function(_cp){var _cq=E(_cp);if(!_cq[0]){return [0];}else{var _cr=E(_cq[2]);return _cr[0]==0?E(_cq):[1,new T(function(){return _ch(_cq[1],_cr[1]);}),new T(function(){return _co(_cr[2]);})];}},_cs=function(_ct){while(1){var _cu=E(_ct);if(!_cu[0]){return _cs(_co(_1));}else{if(!E(_cu[2])[0]){return E(_cu[1]);}else{_ct=_co(_cu);continue;}}}},_cv=function(_cw){var _cx=E(_cw);if(!_cx[0]){return E(_cd);}else{var _cy=_cx[1],_cz=E(_cx[2]);if(!_cz[0]){return [1,_cx,_1];}else{var _cA=_cz[1],_cB=_cz[2];return A(_cf,[_cy,_cA])==2?_cC(_cA,[1,_cy,_1],_cB):_cD(_cA,function(_cE){return [1,_cy,_cE];},_cB);}}},_cF=new T(function(){return _cv(_1);}),_cC=function(_cG,_cH,_cI){while(1){var _cJ=(function(_cK,_cL,_cM){var _cN=E(_cM);if(!_cN[0]){return [1,[1,_cK,_cL],_cF];}else{var _cO=_cN[1];if(A(_cf,[_cK,_cO])==2){_cG=_cO;var _cP=[1,_cK,_cL];_cI=_cN[2];_cH=_cP;return null;}else{return [1,[1,_cK,_cL],new T(function(){return _cv(_cN);})];}}})(_cG,_cH,_cI);if(_cJ!=null){return _cJ;}}},_cD=function(_cQ,_cR,_cS){while(1){var _cT=(function(_cU,_cV,_cW){var _cX=E(_cW);if(!_cX[0]){return [1,new T(function(){return A(_cV,[[1,_cU,_1]]);}),_cF];}else{var _cY=_cX[1],_cZ=_cX[2];switch(A(_cf,[_cU,_cY])){case 0:_cQ=_cY;_cR=function(_d0){return A(_cV,[[1,_cU,_d0]]);};_cS=_cZ;return null;case 1:_cQ=_cY;_cR=function(_d1){return A(_cV,[[1,_cU,_d1]]);};_cS=_cZ;return null;default:return [1,new T(function(){return A(_cV,[[1,_cU,_1]]);}),new T(function(){return _cv(_cX);})];}}})(_cQ,_cR,_cS);if(_cT!=null){return _cT;}}};return _cs(_cv(_cg));},_d2=function(_d3,_d4){var _d5=E(_d3);if(!_d5){return [0];}else{var _d6=E(_d4);return _d6[0]==0?[0]:[1,_d6[1],new T(function(){return _d2(_d5-1|0,_d6[2]);})];}},_d7=function(_d8,_d9,_da){var _db=E(_d9);if(!_db){return _c5(_bT,_ce(_4w,_da));}else{var _dc=_db<=0,_dd=_db>=0;return (function(_de){while(1){var _df=(function(_dg){var _dh=E(_dg);if(!_dh[0]){return [0];}else{var _di=_dh[1],_dj=_dh[2];if(_bq(_di,0)<_db){_de=_dj;return null;}else{var _dk=E(new T(function(){var _dl=_47(function(_4u){return _1I(new T(function(){var _dm=E(_d8);switch(_dm[0]){case 0:return E(_dm[2]);case 1:return E(_0);default:return E(_cc);}}),_4u);},_46);return _dl[0]==0?E(_4k):E(_dl[1]);}))[1],_dn=_47(function(_4u){return _1I(new T(function(){var _do=_1D(_di,0);switch(_do[0]){case 0:return E(_do[2]);case 1:return E(_0);default:return E(_cc);}}),_4u);},_46);if(!_dn[0]){return E(_4k);}else{if(_dk>=E(_dn[1])[1]){var _dp=function(_dq){while(1){var _dr=(function(_ds){var _dt=E(_ds);if(!_dt[0]){return [0];}else{var _du=_dt[1],_dv=_dt[2];if(_bq(_du,0)<_db){_dq=_dv;return null;}else{var _dw=_47(function(_4u){return _1I(new T(function(){var _dx=_1D(_du,0);switch(_dx[0]){case 0:return E(_dx[2]);case 1:return E(_0);default:return E(_cc);}}),_4u);},_46);if(!_dw[0]){return E(_4k);}else{if(_dk>=E(_dw[1])[1]){_dq=_dv;return null;}else{return [1,new T(function(){return !E(_dc)?!E(_dd)?[0]:_d2(_db,_du):[0];}),new T(function(){return _dp(_dv);})];}}}}})(_dq);if(_dr!=null){return _dr;}}};return _dp(_dj);}else{return [1,new T(function(){return !E(_dc)?!E(_dd)?[0]:_d2(_db,_di):[0];}),new T(function(){var _dy=function(_dz){while(1){var _dA=(function(_dB){var _dC=E(_dB);if(!_dC[0]){return [0];}else{var _dD=_dC[1],_dE=_dC[2];if(_bq(_dD,0)<_db){_dz=_dE;return null;}else{var _dF=_47(function(_4u){return _1I(new T(function(){var _dG=_1D(_dD,0);switch(_dG[0]){case 0:return E(_dG[2]);case 1:return E(_0);default:return E(_cc);}}),_4u);},_46);if(!_dF[0]){return E(_4k);}else{if(_dk>=E(_dF[1])[1]){_dz=_dE;return null;}else{return [1,new T(function(){return !E(_dc)?!E(_dd)?[0]:_d2(_db,_dD):[0];}),new T(function(){return _dy(_dE);})];}}}}})(_dz);if(_dA!=null){return _dA;}}};return _dy(_dj);})];}}}}})(_de);if(_df!=null){return _df;}}})(_c5(_bT,_ce(_4w,_da)));}},_dH=function(_dI,_dJ){return [1,_dI,_dJ];},_dK=[2],_dL=[1],_dM=[0],_dN=[1],_dO=unCStr("\u5834\u306b\u51fa\u3066\u3044\u308b\u672d:"),_dP=unCStr("Pattern match failure in do expression at fourKings.hs:369:3-8"),_dQ=unCStr("Pattern match failure in do expression at fourKings.hs:344:3-9"),_dR=unCStr("Pattern match failure in do expression at fourKings.hs:337:3-8"),_dS=unCStr("base"),_dT=unCStr("GHC.Exception"),_dU=unCStr("ArithException"),_dV=[0,I_fromBits([4194982440,719304104]),I_fromBits([3110813675,1843557400]),_dS,_dT,_dU],_dW=[0,I_fromBits([4194982440,719304104]),I_fromBits([3110813675,1843557400]),_dV,_1],_dX=function(_dY){return E(_dW);},_dZ=function(_e0){return E(E(_e0)[1]);},_e1=function(_e2,_e3,_e4){var _e5=new T(function(){var _e6=A(_e2,[_e4]),_e7=A(_e3,[new T(function(){var _e8=E(_e5);return _e8[0]==0?E(_4k):E(_e8[1]);})]),_e9=hs_eqWord64(_e6[1],_e7[1]);if(!E(_e9)){return [0];}else{var _ea=hs_eqWord64(_e6[2],_e7[2]);return E(_ea)==0?[0]:[1,_e4];}});return E(_e5);},_eb=function(_ec){var _ed=E(_ec);return _e1(_dZ(_ed[1]),_dX,_ed[2]);},_ee=unCStr("arithmetic underflow"),_ef=unCStr("arithmetic overflow"),_eg=unCStr("Ratio has zero denominator"),_eh=unCStr("denormal"),_ei=unCStr("divide by zero"),_ej=unCStr("loss of precision"),_ek=function(_el){switch(E(_el)){case 0:return E(_ef);case 1:return E(_ee);case 2:return E(_ej);case 3:return E(_ei);case 4:return E(_eh);default:return E(_eg);}},_em=function(_en){return _W(_ee,_en);},_eo=function(_en){return _W(_ef,_en);},_ep=function(_en){return _W(_eg,_en);},_eq=function(_en){return _W(_eh,_en);},_er=function(_en){return _W(_ei,_en);},_es=function(_en){return _W(_ej,_en);},_et=function(_eu){switch(E(_eu)){case 0:return E(_eo);case 1:return E(_em);case 2:return E(_es);case 3:return E(_er);case 4:return E(_eq);default:return E(_ep);}},_ev=[0,44],_ew=[0,93],_ex=[0,91],_ey=function(_ez,_eA,_eB){var _eC=E(_eA);return _eC[0]==0?unAppCStr("[]",_eB):[1,_ex,new T(function(){return A(_ez,[_eC[1],new T(function(){var _eD=function(_eE){var _eF=E(_eE);return _eF[0]==0?E([1,_ew,_eB]):[1,_ev,new T(function(){return A(_ez,[_eF[1],new T(function(){return _eD(_eF[2]);})]);})];};return _eD(_eC[2]);})]);})];},_eG=function(_eH,_eI){return _ey(_et,_eH,_eI);},_eJ=function(_eK,_eL){switch(E(_eL)){case 0:return E(_eo);case 1:return E(_em);case 2:return E(_es);case 3:return E(_er);case 4:return E(_eq);default:return E(_ep);}},_eM=[0,_eJ,_ek,_eG],_eN=[0,_dX,_eM,_eO,_eb],_eO=function(_en){return [0,_eN,_en];},_eP=3,_eQ=function(_eR,_eS){return die(new T(function(){return A(_eS,[_eR]);}));},_eT=new T(function(){return _eQ(_eP,_eO);}),_eU=unCStr("base"),_eV=unCStr("Control.Exception.Base"),_eW=unCStr("PatternMatchFail"),_eX=[0,I_fromBits([18445595,3739165398]),I_fromBits([52003073,3246954884]),_eU,_eV,_eW],_eY=[0,I_fromBits([18445595,3739165398]),I_fromBits([52003073,3246954884]),_eX,_1],_eZ=function(_f0){return E(_eY);},_f1=function(_f2){var _f3=E(_f2);return _e1(_dZ(_f3[1]),_eZ,_f3[2]);},_f4=function(_f5){return E(E(_f5)[1]);},_f6=function(_f7,_f8){return _W(E(_f7)[1],_f8);},_f9=function(_fa,_fb){return _ey(_f6,_fa,_fb);},_fc=function(_fd,_fe,_ff){return _W(E(_fe)[1],_ff);},_fg=[0,_fc,_f4,_f9],_fh=[0,_eZ,_fg,_fi,_f1],_fi=function(_fj){return [0,_fh,_fj];},_fk=unCStr("Irrefutable pattern failed for pattern"),_fl=[0,32],_fm=[0,10],_fn=[1,_fm,_1],_fo=function(_fp){return E(E(_fp)[1])==124?false:true;},_fq=function(_fr,_fs){var _ft=_bY(_fo,unCStr(_fr)),_fu=_ft[1],_fv=function(_fw,_fx){return _W(_fw,new T(function(){return unAppCStr(": ",new T(function(){return _W(_fs,new T(function(){return _W(_fx,_fn);}));}));}));},_fy=E(_ft[2]);return _fy[0]==0?_fv(_fu,_1):E(E(_fy[1])[1])==124?_fv(_fu,[1,_fl,_fy[2]]):_fv(_fu,_1);},_fz=function(_fA){return _eQ([0,new T(function(){return _fq(_fA,_fk);})],_fi);},_fB=new T(function(){return _fz("fourKings.hs:303:11-36|(lead, x : xs)");}),_fC=function(_fD,_fE){var _fF=_fD%_fE;if(_fD<=0){if(_fD>=0){return E(_fF);}else{if(_fE<=0){return E(_fF);}else{var _fG=E(_fF);return _fG==0?0:_fG+_fE|0;}}}else{if(_fE>=0){if(_fD>=0){return E(_fF);}else{if(_fE<=0){return E(_fF);}else{var _fH=E(_fF);return _fH==0?0:_fH+_fE|0;}}}else{var _fI=E(_fF);return _fI==0?0:_fI+_fE|0;}}},_fJ=function(_fK,_fL,_fM,_fN){while(1){var _fO=(function(_fP,_fQ,_fR,_fS){var _fT=E(_fR);if(!_fT[0]){return E(_fS);}else{var _fU=_fT[1],_fV=E(_fT[2]);if(!_fV[0]){return _W(_fS,[1,_fU,_1]);}else{var _fW=_bq(_fT,0)-1|0;switch(_fW){case -1:var _fX=_bH(0,_fT),_fY=E(_fX[2]);if(!_fY[0]){return E(_fB);}else{var _fZ=(imul(69069,_fP)|0)+1|0;_fL=coercionToken;_fM=new T(function(){return _W(_fX[1],_fY[2]);});var _g0=[1,_fY[1],_fS];_fK=_fZ;_fN=_g0;return null;}break;case 0:return E(_eT);default:var _g1=_fC((imul(214013,_fP)|0)+2531011|0,_fW);if(_g1>=0){var _g2=_bH(_g1,_fT),_g3=E(_g2[2]);if(!_g3[0]){return E(_fB);}else{var _fZ=(imul(69069,_fP)|0)+1|0;_fL=coercionToken;_fM=new T(function(){return _W(_g2[1],_g3[2]);});var _g0=[1,_g3[1],_fS];_fK=_fZ;_fN=_g0;return null;}}else{var _fZ=(imul(69069,_fP)|0)+1|0;_fL=coercionToken;_fM=new T(function(){return _W(_1,_fV);});var _g0=[1,_fU,_fS];_fK=_fZ;_fN=_g0;return null;}}}}})(_fK,_fL,_fM,_fN);if(_fO!=null){return _fO;}}},_g4=function(_g5,_g6,_g7){while(1){var _g8=(function(_g9,_ga,_gb){var _gc=E(_ga);if(!_gc[0]){return E(_gb);}else{var _gd=_gc[1],_ge=E(_gc[2]);if(!_ge[0]){return _W(_gb,[1,_gd,_1]);}else{var _gf=_bq(_gc,0)-1|0;switch(_gf){case -1:var _gg=_bH(0,_gc),_gh=E(_gg[2]);if(!_gh[0]){return E(_fB);}else{_g5=new T(function(){return [0,(imul(69069,E(_g9)[1])|0)+1|0];});_g6=_W(_gg[1],_gh[2]);var _gi=[1,_gh[1],_gb];_g7=_gi;return null;}break;case 0:return E(_eT);default:var _gj=E(_g9)[1],_gk=_fC((imul(214013,_gj)|0)+2531011|0,_gf);if(_gk>=0){var _gl=_bH(_gk,_gc),_gm=E(_gl[2]);return _gm[0]==0?E(_fB):_fJ((imul(69069,_gj)|0)+1|0,coercionToken,new T(function(){return _W(_gl[1],_gm[2]);}),[1,_gm[1],_gb]);}else{return _fJ((imul(69069,_gj)|0)+1|0,coercionToken,new T(function(){return _W(_1,_ge);}),[1,_gd,_gb]);}}}}})(_g5,_g6,_g7);if(_g8!=null){return _g8;}}},_gn=function(_go,_){var _gp=jsRand(),_gq=jsRand();return new T(function(){return _g4(new T(function(){if(_gq<=0.5){var _gr=jsRound(_gp*(-1)*2147483647),_gs=jsRound(_gr&4.294967295e9);return [0,_gs];}else{var _gt=jsRound(_gp*2147483647),_gu=jsRound(_gt&4.294967295e9);return [0,_gu];}}),_go,_1);});},_gv=function(_gw,_gx){switch(E(_gw)){case 0:switch(E(_gx)){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:return E(_gx)==1?true:false;case 2:return E(_gx)==2?true:false;default:return E(_gx)==3?true:false;}},_gy=[0,45],_gz=unCStr("px;"),_gA=function(_gB,_gC){return [1,_gy,new T(function(){return _W(_16(0,E(_gB)[1],_1),new T(function(){return unAppCStr("px ",[1,_gy,new T(function(){return _W(_16(0,E(_gC)[1],_1),_gz);})]);}));})];},_gD=unCStr("px"),_gE=function(_gF,_gG){return [1,_gy,new T(function(){return _W(_16(0,E(_gF)[1],_1),new T(function(){return unAppCStr("px ",[1,_gy,new T(function(){return _W(_16(0,E(_gG)[1],_1),_gD);})]);}));})];},_gH=1,_gI=0,_gJ=2,_gK=3,_gL=[1,_gK,_1],_gM=[1,_gJ,_gL],_gN=[1,_gI,_gM],_gO=[1,_gH,_gN],_gP=unCStr("class"),_gQ=unCStr("card"),_gR=unCStr("background-position"),_gS=unCStr("style"),_gT=[0,60],_gU=[0,1170],_gV=new T(function(){return _gA(_gT,_gU);}),_gW=new T(function(){return _gA(_0,_gU);}),_gX=[0,180],_gY=new T(function(){return _gA(_gX,_gU);}),_gZ=new T(function(){return _gE(_gT,_gU);}),_h0=new T(function(){return _gE(_0,_gU);}),_h1=new T(function(){return _gE(_gX,_gU);}),_h2=[0,97],_h3=[1,_h2,_1],_h4=function(_h5,_){var _h6=jsCreateElem(toJSStr(_h3)),_h7=[0,_h6],_h8=A(_5b,[_5h,_h7,_gP,_gQ,_]),_h9=A(_bB,[_5h,_h7,_gR,new T(function(){var _ha=E(_h5);switch(_ha[0]){case 0:return _gE(new T(function(){var _hb=_47(function(_4u){return _gv(_ha[1],_4u);},_gO);return _hb[0]==0?E(_4k):[0,imul(60,E(_hb[1])[1])|0];}),new T(function(){return [0,imul(90,E(_ha[2])[1]-1|0)|0];}));case 1:return E(E(_ha[1])[1])==0?E(_h0):E(_gZ);default:return E(_h1);}}),_]),_hc=A(_bv,[_5h,_h7,_gS,new T(function(){return unAppCStr("background-position: ",new T(function(){var _hd=E(_h5);switch(_hd[0]){case 0:return _gA(new T(function(){var _he=_47(function(_4u){return _gv(_hd[1],_4u);},_gO);return _he[0]==0?E(_4k):[0,imul(60,E(_he[1])[1])|0];}),new T(function(){return [0,imul(90,E(_hd[2])[1]-1|0)|0];}));case 1:return E(E(_hd[1])[1])==0?E(_gW):E(_gV);default:return E(_gY);}}));}),_]);return _h7;},_hf=unCStr("\u30ab\u30fc\u30c9\u3092\u5ba3\u8a00:"),_hg=unCStr("Pattern match failure in do expression at fourKings.hs:476:7-12"),_hh=unCStr("\u624b\u672d:"),_hi=unCStr("Pattern match failure in do expression at fourKings.hs:448:3-8"),_hj=unCStr("Pattern match failure in do expression at fourKings.hs:391:3-8"),_hk=unCStr("\u5ba3\u8a00\u3055\u308c\u305f\u672d:"),_hl=unCStr(": empty list"),_hm=unCStr("Prelude."),_hn=function(_ho){return err(_W(_hm,new T(function(){return _W(_ho,_hl);})));},_hp=unCStr("head"),_hq=new T(function(){return _hn(_hp);}),_hr=function(_hs){var _ht=E(_hs);switch(_ht[0]){case 0:return E(_ht[2]);case 1:return E(_0);default:return E(_cc);}},_hu=[0,-10],_hv=function(_hw){var _hx=[0,_hw];return [1,[0,_hx,new T(function(){return E(_hw)==13?E(_hu):E(_hx);})],new T(function(){var _hy=E(_hw);return _hy==13?[0]:_hv(_hy+1|0);})];},_hz=new T(function(){return _hv(0);}),_hA=new T(function(){return _P(_7,_hz);}),_hB=[0,15],_hC=[0,20],_hD=[0,30],_hE=[0,40],_hF=function(_hG){var _hH=E(_hG);if(!_hH[0]){return E(_hA);}else{var _hI=_hH[1],_hJ=_hH[2],_hK=[0,new T(function(){var _hL=E(_hI);switch(_hL[0]){case 0:return E(_hL[2]);case 1:return E(_0);default:return E(_cc);}}),new T(function(){switch(_bq(_hJ,0)){case 0:return E(_hE);case 1:return E(_hD);case 2:return E(_hC);case 3:return E(_hB);default:return E(_0);}})],_hM=E(_hI);switch(_hM[0]){case 0:return _7z(function(_hN){return E(_hK);},E(_hM[2])[1],_hF(_hJ));case 1:return _7z(function(_hO){return E(_hK);},0,_hF(_hJ));default:return _7z(function(_hP){return E(_hK);},-1,_hF(_hJ));}}},_hQ=function(_hR,_hS,_hT){var _hU=E(_hT);if(!_hU[0]){return [0];}else{var _hV=_hU[1],_hW=_hU[2];return !A(_hR,[_hS,_hV])?[1,_hV,new T(function(){return _hQ(_hR,_hS,_hW);})]:E(_hW);}},_hX=function(_hY,_hZ){while(1){var _i0=E(_hY);if(!_i0[0]){return E(_hZ);}else{_hY=_i0[2];var _i1=_hQ(_1L,_i0[1],_hZ);_hZ=_i1;continue;}}},_i2=function(_i3,_i4){return _i3<=0?_i3>=0?quot(_i3,_i4):_i4<=0?quot(_i3,_i4):quot(_i3+1|0,_i4)-1|0:_i4>=0?_i3>=0?quot(_i3,_i4):_i4<=0?quot(_i3,_i4):quot(_i3+1|0,_i4)-1|0:quot(_i3-1|0,_i4)-1|0;},_i5=[1,_dN,_1],_i6=[1,_dN,_i5],_i7=[1,_dN,_i6],_i8=function(_i9,_ia,_ib){while(1){var _ic=E(_ib);if(!_ic[0]){return false;}else{if(!A(_1Z,[_i9,_ia,_ic[1]])){_ib=_ic[2];continue;}else{return true;}}}},_id=unCStr("base"),_ie=unCStr("GHC.IO.Exception"),_if=unCStr("IOException"),_ig=[0,I_fromBits([4053623282,1685460941]),I_fromBits([3693590983,2507416641]),_id,_ie,_if],_ih=[0,I_fromBits([4053623282,1685460941]),I_fromBits([3693590983,2507416641]),_ig,_1],_ii=function(_ij){return E(_ih);},_ik=function(_il){var _im=E(_il);return _e1(_dZ(_im[1]),_ii,_im[2]);},_in=unCStr(": "),_io=[0,41],_ip=unCStr(" ("),_iq=unCStr("already exists"),_ir=unCStr("does not exist"),_is=unCStr("protocol error"),_it=unCStr("failed"),_iu=unCStr("invalid argument"),_iv=unCStr("inappropriate type"),_iw=unCStr("hardware fault"),_ix=unCStr("unsupported operation"),_iy=unCStr("timeout"),_iz=unCStr("resource vanished"),_iA=unCStr("interrupted"),_iB=unCStr("resource busy"),_iC=unCStr("resource exhausted"),_iD=unCStr("end of file"),_iE=unCStr("illegal operation"),_iF=unCStr("permission denied"),_iG=unCStr("user error"),_iH=unCStr("unsatisified constraints"),_iI=unCStr("system error"),_iJ=function(_iK,_iL){switch(E(_iK)){case 0:return _W(_iq,_iL);case 1:return _W(_ir,_iL);case 2:return _W(_iB,_iL);case 3:return _W(_iC,_iL);case 4:return _W(_iD,_iL);case 5:return _W(_iE,_iL);case 6:return _W(_iF,_iL);case 7:return _W(_iG,_iL);case 8:return _W(_iH,_iL);case 9:return _W(_iI,_iL);case 10:return _W(_is,_iL);case 11:return _W(_it,_iL);case 12:return _W(_iu,_iL);case 13:return _W(_iv,_iL);case 14:return _W(_iw,_iL);case 15:return _W(_ix,_iL);case 16:return _W(_iy,_iL);case 17:return _W(_iz,_iL);default:return _W(_iA,_iL);}},_iM=[0,125],_iN=unCStr("{handle: "),_iO=function(_iP,_iQ,_iR,_iS,_iT,_iU){var _iV=new T(function(){var _iW=new T(function(){return _iJ(_iQ,new T(function(){var _iX=E(_iS);return _iX[0]==0?E(_iU):_W(_ip,new T(function(){return _W(_iX,[1,_io,_iU]);}));}));}),_iY=E(_iR);return _iY[0]==0?E(_iW):_W(_iY,new T(function(){return _W(_in,_iW);}));}),_iZ=E(_iT);if(!_iZ[0]){var _j0=E(_iP);if(!_j0[0]){return E(_iV);}else{var _j1=E(_j0[1]);return _j1[0]==0?_W(_iN,new T(function(){return _W(_j1[1],[1,_iM,new T(function(){return _W(_in,_iV);})]);})):_W(_iN,new T(function(){return _W(_j1[1],[1,_iM,new T(function(){return _W(_in,_iV);})]);}));}}else{return _W(_iZ[1],new T(function(){return _W(_in,_iV);}));}},_j2=function(_j3){var _j4=E(_j3);return _iO(_j4[1],_j4[2],_j4[3],_j4[4],_j4[6],_1);},_j5=function(_j6,_j7){var _j8=E(_j6);return _iO(_j8[1],_j8[2],_j8[3],_j8[4],_j8[6],_j7);},_j9=function(_ja,_jb){return _ey(_j5,_ja,_jb);},_jc=function(_jd,_je,_jf){var _jg=E(_je);return _iO(_jg[1],_jg[2],_jg[3],_jg[4],_jg[6],_jf);},_jh=[0,_jc,_j2,_j9],_ji=[0,_ii,_jh,_jj,_ik],_jj=function(_jk){return [0,_ji,_jk];},_jl=[0],_jm=7,_jn=function(_jo){return [0,_jl,_jm,_1,_jo,_jl,_jl];},_jp=function(_jq,_){return die(new T(function(){return _jj(new T(function(){return _jn(_jq);}));}));},_jr=function(_js,_){return _jp(_js,_);},_jt=function(_ju){return [0];},_jv=function(_jw,_jx){while(1){var _jy=(function(_jz,_jA){var _jB=E(_jA);if(!_jB[0]){return E(_jz);}else{var _jC=E(_jB[1]),_jD=E(_jC[1])[1],_jE=_7z(function(_jF){return E(new T(function(){var _jG=_b5(_jz,_jD);return [0,_jC[2],_jG[2],_jG[3]];}));},_jD,_jz);_jx=_jB[2];_jw=_jE;return null;}})(_jw,_jx);if(_jy!=null){return _jy;}}},_jH=function(_jI,_jJ,_jK){while(1){var _jL=E(_jK);if(!_jL[0]){return [0];}else{var _jM=E(_jL[1]);if(!A(_1Z,[_jI,_jJ,_jM[1]])){_jK=_jL[2];continue;}else{return [1,_jM[2]];}}}},_jN=unCStr("otherhands"),_jO=unCStr("\u8a66\u5408\u76ee/"),_jP=[0,112],_jQ=[1,_jP,_1],_jR=[1,_jP,_1],_jS=unCStr("header"),_jT=function(_jU,_jV,_jW){var _jX=E(_jW);return !E(_jU)?A(_jV,[[0,_jX[1]+1|0]]):[1,_jX];},_jY=new T(function(){return [0,_fC(1,4)];}),_jZ=[2,_jY],_k0=unCStr("disabled"),_k1=unCStr("\u30d1\u30b9"),_k2=unCStr("ball"),_k3=unCStr("18px"),_k4=unCStr("font-size"),_k5=unCStr("5px"),_k6=unCStr("margin-left"),_k7=unCStr("declared"),_k8=unCStr("gained"),_k9=unCStr("\u30cb\u30e5\u30fc\u30b2\u30fc\u30e0"),_ka=unCStr("cards"),_kb=unCStr("hands"),_kc=unCStr("now"),_kd=unCStr("display: block;"),_ke=unCStr("block"),_kf=unCStr("display"),_kg=unCStr("display: none;"),_kh=unCStr("none"),_ki=unCStr("\u81ea\u5206"),_kj=unCStr("\u5bfe\u6226\u6210\u7e3e"),_kk=unCStr("layouted"),_kl=[0,58],_km=[1,_kl,_1],_kn=unCStr("\u30bf\u30fc\u30f3"),_ko=unCStr("\u30b2\u30fc\u30e0\u958b\u59cb\uff01"),_kp=unCStr("\u30b2\u30fc\u30e0\u7d42\u4e86\uff01"),_kq=[0,_gI,_3S],_kr=function(_ks){return _i8(_1Y,_kq,E(_ks)[1]);},_kt=new T(function(){return _1h(0,2147483647);}),_ku=unCStr("button"),_kv=[1,_jP,_1],_kw=unCStr("div"),_kx=[2,_jY],_ky=new T(function(){return _16(0,0,_1);}),_kz=new T(function(){return _16(0,-1,_1);}),_kA=unCStr("span"),_kB=function(_kC,_kD){return !_1L(_kC,_kD)?_4l(_kC,_kD):false;},_kE=function(_kF,_kG){return !_1L(_kF,_kG)?!_4l(_kF,_kG)?true:false:false;},_kH=function(_kI,_kJ){return !_1L(_kI,_kJ)?!_4l(_kI,_kJ)?true:false:true;},_kK=function(_kL,_kM){return !_4l(_kL,_kM)?E(_kL):E(_kM);},_kN=function(_kO,_kP){return !_4l(_kO,_kP)?E(_kP):E(_kO);},_kQ=[0,_1Y,_4w,_kB,_kH,_kE,_4l,_kK,_kN],_kR=function(_kS){return E(E(_kS)[2]);},_kT=function(_kU,_kV,_kW){while(1){var _kX=E(_kV);if(!_kX[0]){return E(_kW)[0]==0?1:0;}else{var _kY=E(_kW);if(!_kY[0]){return 2;}else{var _kZ=A(_kR,[_kU,_kX[1],_kY[1]]);if(_kZ==1){_kV=_kX[2];_kW=_kY[2];continue;}else{return E(_kZ);}}}}},_l0=function(_l1,_l2){return _kT(_kQ,_l1,_l2);},_l3=function(_l4){return [0,_1,_1,E(_l4)[3]];},_l5=unCStr("newGame"),_l6=[1,_jP,_1],_l7=function(_l8,_l9){return _bq(_l9,0)==0?_H(_l8,_l9):E(_l8);},_la=function(_lb){return E(E(_lb)[1]);},_lc=new T(function(){return _1h(0,-1);}),_ld=new T(function(){return _1h(0,0);}),_le=unCStr("td"),_lf=unCStr("tr"),_lg=unCStr("th"),_lh=unCStr("caption"),_li=unCStr("table"),_lj=[1,_jP,_1],_lk=[1,_jP,_1],_ll=unCStr("layouts"),_lm=[1,_jP,_1],_ln=0,_lo=new T(function(){return _eQ(_ln,_eO);}),_lp=new T(function(){return [0,"click"];}),_lq=function(_lr,_ls){var _lt=A(_lr,[_ls]);if(!_lt[0]){return [0];}else{var _lu=E(_lt[1]);return [1,_lu[1],new T(function(){return _lq(_lr,_lu[2]);})];}},_lv=function(_lw,_lx){var _ly=E(_lw);if(!_ly[0]){return [0];}else{var _lz=E(_lx);return _lz[0]==0?[0]:[1,[0,_ly[1],_lz[1]],new T(function(){return _lv(_ly[2],_lz[2]);})];}},_lA=function(_lB,_){var _lC=rMV(_lB),_lD=E(_lC),_lE=_lD[1],_lF=_lD[4],_lG=_lD[5],_lH=_lD[6],_lI=_lD[7],_lJ=_lD[8],_lK=_lD[9],_lL=function(_){var _lM=rMV(_lB),_lN=E(_lM),_lO=_lN[1],_lP=_lN[3],_lQ=_lN[9],_lR=function(_){var _lS=rMV(_lB),_lT=jsFind(toJSStr(E(_jS))),_lU=function(_){var _lV=rMV(_lB),_lW=E(_lV),_lX=_lW[1],_lY=_lW[2],_lZ=_lW[4],_m0=_lW[5],_m1=_lW[6],_m2=_lW[7],_m3=_lW[8],_m4=_lW[9],_m5=E(_lW[3]);if(_m5[0]==2){var _=wMV(_lB,new T(function(){var _m6=E(_m5[1]),_m7=_m6[1],_m8=_d7(new T(function(){return _1D(_m1,0);}),_bq(_m1,0),_b5(_lX,_m7)[1]);if(!_m8[0]){return [0,_lX,_lY,[2,new T(function(){return [0,_fC(_m7+1|0,4)];})],_lZ,_m0,_m1,new T(function(){return [0,E(_m2)[1]+1|0];}),_m3,[1,_dN,_m4]];}else{var _m9=new T(function(){return _1D(_m8,0);});return [0,new T(function(){return _7z(function(_ma){var _mb=E(_ma);return [0,new T(function(){return _hX(_m9,_mb[1]);}),_mb[2],_mb[3]];},_m7,_lX);}),_lY,[2,new T(function(){return [0,_fC(_m7+1|0,4)];})],_lZ,new T(function(){return _W(_m0,[1,[0,_m6,_m9],_1]);}),_m9,new T(function(){return [0,E(_m2)[1]+1|0];}),_m3,[1,[2,_m9],_m4]];}}));return _5a;}else{return _5a;}},_mc=[0,function(_){return _lA(_lB,_);}],_md=function(_){var _me=rMV(_lB),_mf=E(_kb),_mg=jsFind(toJSStr(_mf)),_mh=E(_mg);if(!_mh[0]){return _jr(_hi,_);}else{var _mi=_mh[1],_mj=E(_me),_mk=_mj[1],_ml=_mj[3],_mm=_mj[6],_mn=function(_){var _mo=jsCreateElem(toJSStr(_l6)),_mp=jsSetInnerText(_mo,toJSStr(E(_hh))),_mq=E(_mi)[1],_mr=jsAppendChild(_mo,_mq),_ms=E(_kw),_mt=jsCreateElem(toJSStr(_ms)),_mu=A(_5b,[_5h,[0,_mt],_gP,_mf,_]),_mv=jsAppendChild(_mt,_mq),_mw=function(_mx,_){while(1){var _my=E(_mx);if(!_my[0]){return _5a;}else{var _mz=_h4(_my[1],_),_mA=jsAppendChild(E(_mz)[1],_mt);_mx=_my[2];continue;}}},_mB=new T(function(){return _ce(_4w,_b5(_mk,0)[1]);}),_mC=function(_){var _mD=function(_){return _lA(_lB,_);},_mE=function(_){var _mF=jsCreateElem(toJSStr(_ms)),_mG=A(_5b,[_5h,[0,_mF],_gP,_k8,_]),_mH=jsAppendChild(_mF,_mq),_mI=(function(_mJ,_){while(1){var _mK=E(_mJ);if(!_mK[0]){return _5a;}else{var _mL=_h4(_mK[1],_),_mM=jsAppendChild(E(_mL)[1],_mF);_mJ=_mK[2];continue;}}})(_b5(_mk,0)[2],_),_mN=rMV(_lB),_mO=jsCreateElem(toJSStr(_ms)),_mP=A(_5b,[_5h,[0,_mO],_gP,_k7,_]),_mQ=jsAppendChild(_mO,_mq),_mR=E(_mN),_mS=_mR[8];if(!E(E(_mR[2])[1])){if(_bq(_mS,0)>=4){return _5a;}else{var _mT=jsCreateElem(toJSStr(_kv)),_mU=jsSetInnerText(_mT,toJSStr(E(_hf))),_mV=jsAppendChild(_mT,_mO),_mW=new T(function(){return _8u(_hr,_mS);}),_mX=[0,_mD],_mY=function(_mZ,_){while(1){var _n0=(function(_n1,_){var _n2=E(_n1);if(!_n2[0]){return _5a;}else{var _n3=_n2[2],_n4=new T(function(){var _n5=E(_n2[1]);return _n5[0]==0?E(_hq):E(_n5[1]);});if(!_i8(_3n,new T(function(){return _hr(_n4);}),_mW)){var _n6=E(_ku),_n7=jsCreateElem(toJSStr(_n6)),_n8=jsAppendChild(_n7,_mO),_n9=jsSetInnerText(_n7,toJSStr(_54(_n4))),_na=[0,_n7],_nb=A(_bB,[_5h,_na,_k6,_k5,_]),_nc=A(_bB,[_5h,_na,_k4,_k3,_]),_nd=rMV(_lB),_ne=E(_lp)[1],_nf=jsSetCB(_n7,_ne,function(_ng,_nh,_){var _=wMV(_lB,new T(function(){var _ni=E(_nd);return [0,new T(function(){return _7z(function(_nj){var _nk=E(_nj);return [0,new T(function(){return _hQ(_1L,_n4,_nk[1]);}),_nk[2],_nk[3]];},0,_ni[1]);}),_ni[2],_ni[3],_ni[4],_ni[5],_ni[6],_ni[7],[1,_n4,_ni[8]],_ni[9]];})),_nl=jsSetTimeout(150,E(_mX)[1]);return _5a;});return (function(_nm,_){while(1){var _nn=(function(_no,_){var _np=E(_no);if(!_np[0]){return _5a;}else{var _nq=_np[2],_nr=new T(function(){var _ns=E(_np[1]);return _ns[0]==0?E(_hq):E(_ns[1]);});if(!_i8(_3n,new T(function(){return _hr(_nr);}),_mW)){var _nt=jsCreateElem(toJSStr(_n6)),_nu=jsAppendChild(_nt,_mO),_nv=jsSetInnerText(_nt,toJSStr(_54(_nr))),_nw=[0,_nt],_nx=A(_bB,[_5h,_nw,_k6,_k5,_]),_ny=A(_bB,[_5h,_nw,_k4,_k3,_]),_nz=rMV(_lB),_nA=jsSetCB(_nt,_ne,function(_nB,_nC,_){var _=wMV(_lB,new T(function(){var _nD=E(_nz);return [0,new T(function(){return _7z(function(_nE){var _nF=E(_nE);return [0,new T(function(){return _hQ(_1L,_nr,_nF[1]);}),_nF[2],_nF[3]];},0,_nD[1]);}),_nD[2],_nD[3],_nD[4],_nD[5],_nD[6],_nD[7],[1,_nr,_nD[8]],_nD[9]];})),_nG=jsSetTimeout(150,E(_mX)[1]);return _5a;});_nm=_nq;return null;}else{_nm=_nq;return null;}}})(_nm,_);if(_nn!=null){return _nn;}}})(_n3,_);}else{_mZ=_n3;return null;}}})(_mZ,_);if(_n0!=null){return _n0;}}};if(E(_mR[3])[0]==2){return _mY(_c5(_1L,_ce(_4w,_mB)),_);}else{var _nH=A(_5b,[_5h,[0,_mT],_k0,_k0,_]);return _mY(_c5(_1L,_ce(_4w,_mB)),_);}}}else{return _5a;}},_nI=E(_ml);switch(_nI[0]){case 2:if(!E(E(_nI[1])[1])){var _nJ=jsCreateElem(toJSStr(E(_ku))),_nK=A(_5b,[_5h,[0,_nJ],_gP,_k2,_]),_nL=jsSetInnerText(_nJ,toJSStr(E(_k1))),_nM=jsAppendChild(_nJ,_mt),_nN=rMV(_lB),_nO=E(_lp)[1],_nP=jsSetCB(_nJ,_nO,function(_nQ,_nR,_){var _=wMV(_lB,new T(function(){var _nS=E(_nN);return [0,_nS[1],_nS[2],_jZ,_nS[4],_nS[5],_nS[6],new T(function(){return [0,E(_nS[7])[1]+1|0];}),_nS[8],[1,_dN,_nS[9]]];})),_nT=jsSetTimeout(150,E([0,function(_){return _lA(_lB,_);}])[1]);return _5a;}),_nU=new T(function(){return _1D(_mm,0);}),_nV=new T(function(){return [0,_bq(_mm,0)];}),_nW=new T(function(){return _d7(_nU,E(_nV)[1],_mB);}),_nX=[0,_mD],_nY=function(_nZ){while(1){var _o0=(function(_o1){var _o2=E(_o1);if(!_o2[0]){return E(_nW);}else{var _o3=_o2[1],_o4=_o2[2];if(!_i8(_1Y,_o3,new T(function(){return _8r(_d7(_nU,E(_nV)[1],_mB));}))){return [1,[1,_o3,_1],new T(function(){return _nY(_o4);})];}else{_nZ=_o4;return null;}}})(_nZ);if(_o0!=null){return _o0;}}},_o5=_ce(_l0,_nY(_mB));if(!_o5[0]){return _mE(_);}else{var _o6=_o5[1],_o7=E(_kA),_o8=jsCreateElem(toJSStr(_o7)),_o9=A(_5b,[_5h,[0,_o8],_gP,_ka,_]),_oa=jsAppendChild(_o8,_mt),_ob=[2,_o6],_oc=function(_od){var _oe=E(_od);return [0,new T(function(){return _hX(_o6,_oe[1]);}),_oe[2],_oe[3]];},_of=function(_){var _og=(function(_oh,_){while(1){var _oi=(function(_oj,_){var _ok=E(_oj);if(!_ok[0]){return _5a;}else{var _ol=_ok[1],_om=_ok[2],_on=jsCreateElem(toJSStr(_o7)),_oo=A(_5b,[_5h,[0,_on],_gP,_ka,_]),_op=jsAppendChild(_on,_mt),_oq=[2,_ol],_or=function(_os){var _ot=E(_os);return [0,new T(function(){return _hX(_ol,_ot[1]);}),_ot[2],_ot[3]];},_ou=E(_ol);if(!_ou[0]){_oh=_om;return null;}else{var _ov=_ou[1],_ow=_ou[2],_ox=_h4(_ov,_),_oy=E(_ox)[1],_oz=jsAppendChild(_oy,_on);if(!_i8(_2f,_ou,_nW)){var _oA=(function(_oB,_){while(1){var _oC=E(_oB);if(!_oC[0]){return _5a;}else{var _oD=_h4(_oC[1],_),_oE=jsAppendChild(E(_oD)[1],_on);_oB=_oC[2];continue;}}})(_ow,_);_oh=_om;return null;}else{var _oF=rMV(_lB),_oG=_5k(_oy,_gP,new T(function(){return unAppCStr("button-",new T(function(){var _oH=E(_ov);switch(_oH[0]){case 0:return _16(0,E(_oH[2])[1],_1);case 1:return E(_ky);default:return E(_kz);}}));}),_),_oI=rMV(_lB),_oJ=jsSetCB(_oy,_nO,function(_oK,_oL,_){var _=wMV(_lB,new T(function(){var _oM=E(_oI);return [0,new T(function(){return _7z(_or,0,_oM[1]);}),_oM[2],_kx,_oM[4],new T(function(){return _W(_oM[5],[1,[0,new T(function(){var _oN=E(_oM[3]);return _oN[0]==2?E(_oN[1]):E(_8B);}),_ou],_1]);}),_ou,new T(function(){return [0,E(_oM[7])[1]+1|0];}),_oM[8],[1,_oq,_oM[9]]];})),_oO=jsSetTimeout(150,E(_nX)[1]);return _5a;}),_oP=(function(_oQ,_){while(1){var _oR=(function(_oS,_){var _oT=E(_oS);if(!_oT[0]){return _5a;}else{var _oU=_oT[1],_oV=_h4(_oU,_),_oW=E(_oV)[1],_oX=jsAppendChild(_oW,_on),_oY=rMV(_lB),_oZ=_5k(_oW,_gP,new T(function(){return unAppCStr("button-",new T(function(){var _p0=E(_oU);switch(_p0[0]){case 0:return _16(0,E(_p0[2])[1],_1);case 1:return E(_ky);default:return E(_kz);}}));}),_),_p1=rMV(_lB),_p2=jsSetCB(_oW,_nO,function(_p3,_p4,_){var _=wMV(_lB,new T(function(){var _p5=E(_p1);return [0,new T(function(){return _7z(_or,0,_p5[1]);}),_p5[2],_kx,_p5[4],new T(function(){return _W(_p5[5],[1,[0,new T(function(){var _p6=E(_p5[3]);return _p6[0]==2?E(_p6[1]):E(_8B);}),_ou],_1]);}),_ou,new T(function(){return [0,E(_p5[7])[1]+1|0];}),_p5[8],[1,_oq,_p5[9]]];})),_p7=jsSetTimeout(150,E(_nX)[1]);return _5a;});_oQ=_oT[2];return null;}})(_oQ,_);if(_oR!=null){return _oR;}}})(_ow,_);_oh=_om;return null;}}}})(_oh,_);if(_oi!=null){return _oi;}}})(_o5[2],_);return _mE(_);},_p8=E(_o6);if(!_p8[0]){return _of(_);}else{var _p9=_p8[1],_pa=_p8[2],_pb=_h4(_p9,_),_pc=E(_pb)[1],_pd=jsAppendChild(_pc,_o8);if(!_i8(_2f,_p8,_nW)){var _pe=(function(_pf,_){while(1){var _pg=E(_pf);if(!_pg[0]){return _5a;}else{var _ph=_h4(_pg[1],_),_pi=jsAppendChild(E(_ph)[1],_o8);_pf=_pg[2];continue;}}})(_pa,_);return _of(_);}else{var _pj=rMV(_lB),_pk=_5k(_pc,_gP,new T(function(){return unAppCStr("button-",new T(function(){var _pl=E(_p9);switch(_pl[0]){case 0:return _16(0,E(_pl[2])[1],_1);case 1:return E(_ky);default:return E(_kz);}}));}),_),_pm=rMV(_lB),_pn=jsSetCB(_pc,_nO,function(_po,_pp,_){var _=wMV(_lB,new T(function(){var _pq=E(_pm);return [0,new T(function(){return _7z(_oc,0,_pq[1]);}),_pq[2],_kx,_pq[4],new T(function(){return _W(_pq[5],[1,[0,new T(function(){var _pr=E(_pq[3]);return _pr[0]==2?E(_pr[1]):E(_8B);}),_p8],_1]);}),_p8,new T(function(){return [0,E(_pq[7])[1]+1|0];}),_pq[8],[1,_ob,_pq[9]]];})),_ps=jsSetTimeout(150,E(_nX)[1]);return _5a;}),_pt=(function(_pu,_){while(1){var _pv=(function(_pw,_){var _px=E(_pw);if(!_px[0]){return _5a;}else{var _py=_px[1],_pz=_h4(_py,_),_pA=E(_pz)[1],_pB=jsAppendChild(_pA,_o8),_pC=rMV(_lB),_pD=_5k(_pA,_gP,new T(function(){return unAppCStr("button-",new T(function(){var _pE=E(_py);switch(_pE[0]){case 0:return _16(0,E(_pE[2])[1],_1);case 1:return E(_ky);default:return E(_kz);}}));}),_),_pF=rMV(_lB),_pG=jsSetCB(_pA,_nO,function(_pH,_pI,_){var _=wMV(_lB,new T(function(){var _pJ=E(_pF);return [0,new T(function(){return _7z(_oc,0,_pJ[1]);}),_pJ[2],_kx,_pJ[4],new T(function(){return _W(_pJ[5],[1,[0,new T(function(){var _pK=E(_pJ[3]);return _pK[0]==2?E(_pK[1]):E(_8B);}),_p8],_1]);}),_p8,new T(function(){return [0,E(_pJ[7])[1]+1|0];}),_pJ[8],[1,_ob,_pJ[9]]];})),_pL=jsSetTimeout(150,E(_nX)[1]);return _5a;});_pu=_px[2];return null;}})(_pu,_);if(_pv!=null){return _pv;}}})(_pa,_);return _of(_);}}}}else{return _mE(_);}break;case 3:var _pM=jsFind(toJSStr(E(_l5))),_pN=E(_pM);if(!_pN[0]){var _pO=_jr(_hg,_);return _mE(_);}else{var _pP=jsCreateElem(toJSStr(E(_ku))),_pQ=A(_5b,[_5h,[0,_pP],_gP,_k2,_]),_pR=E(_pN[1])[1],_pS=jsAppendChild(_pP,_pR),_pT=jsSetInnerText(_pP,toJSStr(E(_k9))),_pU=jsSetCB(_pP,E(_lp)[1],function(_pV,_pW,_){var _pX=jsClearChildren(_pR),_pY=rMV(_lB),_=wMV(_lB,new T(function(){var _pZ=E(_pY);return [0,new T(function(){return _2k(_l3,_pZ[1]);}),_pZ[2],_dM,_1x,_1,_1,_3C,_1,_pZ[9]];})),_q0=jsSetTimeout(150,E(_mc)[1]);return _5a;});return _mE(_);}break;default:return _mE(_);}},_q1=E(_ml);if(_q1[0]==2){if(!E(E(_q1[1])[1])){return _mC(_);}else{var _q2=jsCreateElem(toJSStr(E(_ku))),_q3=[0,_q2],_q4=A(_5b,[_5h,_q3,_gP,_k2,_]),_q5=jsSetInnerText(_q2,toJSStr(E(_k1))),_q6=jsAppendChild(_q2,_mt),_q7=A(_5b,[_5h,_q3,_k0,_k0,_]),_q8=rMV(_lB),_q9=jsSetCB(_q2,E(_lp)[1],function(_qa,_qb,_){var _=wMV(_lB,new T(function(){var _qc=E(_q8);return [0,_qc[1],_qc[2],_jZ,_qc[4],_qc[5],_qc[6],new T(function(){return [0,E(_qc[7])[1]+1|0];}),_qc[8],[1,_dN,_qc[9]]];})),_qd=jsSetTimeout(150,E([0,function(_){return _lA(_lB,_);}])[1]);return _5a;}),_qe=_mw(_mB,_);return _mC(_);}}else{var _qf=jsCreateElem(toJSStr(E(_ku))),_qg=[0,_qf],_qh=A(_5b,[_5h,_qg,_gP,_k2,_]),_qi=jsSetInnerText(_qf,toJSStr(E(_k1))),_qj=jsAppendChild(_qf,_mt),_qk=A(_5b,[_5h,_qg,_k0,_k0,_]),_ql=rMV(_lB),_qm=jsSetCB(_qf,E(_lp)[1],function(_qn,_qo,_){var _=wMV(_lB,new T(function(){var _qp=E(_ql);return [0,_qp[1],_qp[2],_jZ,_qp[4],_qp[5],_qp[6],new T(function(){return [0,E(_qp[7])[1]+1|0];}),_qp[8],[1,_dN,_qp[9]]];})),_qq=jsSetTimeout(150,E([0,function(_){return _lA(_lB,_);}])[1]);return _5a;}),_qr=_mw(_mB,_);return _mC(_);}},_qs=E(_ml);if(_qs[0]==2){if(!E(E(_qs[1])[1])){var _qt=A(_5b,[_5h,_mi,_gP,_kc,_]),_qu=jsClearChildren(E(_mi)[1]);return _mn(_);}else{var _qv=jsClearChildren(E(_mi)[1]);return _mn(_);}}else{var _qw=jsClearChildren(E(_mi)[1]);return _mn(_);}}},_qx=E(_lT);if(!_qx[0]){var _qy=_jr(_dR,_),_qz=rMV(_lB),_qA=E(_qz)[3],_qB=function(_){var _qC=E(_qA);switch(_qC[0]){case 2:if(!E(E(_qC[1])[1])){return _5a;}else{var _qD=jsSetTimeout(150,E(_mc)[1]);return _5a;}break;case 3:return _5a;default:var _qE=jsSetTimeout(150,E(_mc)[1]);return _5a;}},_qF=function(_){var _qG=E(_qA);if(_qG[0]==2){if(!E(E(_qG[1])[1])){var _qH=_md(_);return _qB(_);}else{var _qI=_lU(_);return _qB(_);}}else{var _qJ=_lU(_);return _qB(_);}};switch(E(_qA)[0]){case 2:return _qF(_);case 3:var _qK=_md(_);return _qB(_);default:return _qF(_);}}else{var _qL=E(_qx[1])[1],_qM=jsClearChildren(_qL),_qN=jsCreateElem(toJSStr(_jR)),_qO=E(_lS),_qP=_qO[1],_qQ=_qO[3],_qR=function(_qS){var _qT=jsSetInnerText(_qN,toJSStr(_qS)),_qU=jsCreateElem(toJSStr(_jQ)),_qV=_b5(_qP,0)[3],_qW=jsSetInnerText(_qU,toJSStr(_W(_16(0,_bq(_qV,0)+1|0,_1),new T(function(){return _W(_jO,new T(function(){return _W(_16(0,_i2(E(_qO[7])[1]+1|0,4),_1),_kn);}));})))),_qX=jsAppendChild(_qN,_qL),_qY=jsAppendChild(_qU,_qL),_qZ=jsFind(toJSStr(E(_jN))),_r0=E(_qZ);if(!_r0[0]){var _r1=_jr(_dQ,_),_r2=rMV(_lB),_r3=E(_r2)[3],_r4=function(_){var _r5=E(_r3);switch(_r5[0]){case 2:if(!E(E(_r5[1])[1])){return _5a;}else{var _r6=jsSetTimeout(150,E(_mc)[1]);return _5a;}break;case 3:return _5a;default:var _r7=jsSetTimeout(150,E(_mc)[1]);return _5a;}},_r8=function(_){var _r9=E(_r3);if(_r9[0]==2){if(!E(E(_r9[1])[1])){var _ra=_md(_);return _r4(_);}else{var _rb=_lU(_);return _r4(_);}}else{var _rc=_lU(_);return _r4(_);}};switch(E(_r3)[0]){case 2:return _r8(_);case 3:var _rd=_md(_);return _r4(_);default:return _r8(_);}}else{var _re=E(_r0[1])[1],_rf=jsClearChildren(_re),_rg=function(_){var _rh=jsFind(toJSStr(E(_ll))),_ri=E(_rh);if(!_ri[0]){var _rj=_jr(_dP,_),_rk=rMV(_lB),_rl=E(_rk)[3],_rm=function(_){var _rn=E(_rl);switch(_rn[0]){case 2:if(!E(E(_rn[1])[1])){return _5a;}else{var _ro=jsSetTimeout(150,E(_mc)[1]);return _5a;}break;case 3:return _5a;default:var _rp=jsSetTimeout(150,E(_mc)[1]);return _5a;}},_rq=function(_){var _rr=E(_rl);if(_rr[0]==2){if(!E(E(_rr[1])[1])){var _rs=_md(_);return _rm(_);}else{var _rt=_lU(_);return _rm(_);}}else{var _ru=_lU(_);return _rm(_);}};switch(E(_rl)[0]){case 2:return _rq(_);case 3:var _rv=_md(_);return _rm(_);default:return _rq(_);}}else{var _rw=E(_ri[1])[1],_rx=jsClearChildren(_rw),_ry=E(_kw),_rz=jsCreateElem(toJSStr(_ry)),_rA=A(_5b,[_5h,[0,_rz],_gP,_kk,_]),_rB=jsAppendChild(_rz,_rw),_rC=jsCreateElem(toJSStr(_lk)),_rD=jsSetInnerText(_rC,toJSStr(E(_dO))),_rE=jsAppendChild(_rC,_rz),_rF=(function(_rG,_){while(1){var _rH=(function(_rI,_){var _rJ=E(_rI);if(!_rJ[0]){return _5a;}else{var _rK=E(_rJ[1]),_rL=(function(_rM,_){while(1){var _rN=E(_rM);if(!_rN[0]){return _5a;}else{var _rO=_h4(_rN[1],_),_rP=E(_rO)[1],_rQ=jsAppendChild(_rP,_rz),_rR=_5k(_rP,_gP,new T(function(){return unAppCStr("player-",new T(function(){return _16(0,E(_rK[1])[1],_1);}));}),_);_rM=_rN[2];continue;}}})(_rK[2],_);_rG=_rJ[2];return null;}})(_rG,_);if(_rH!=null){return _rH;}}})(_qO[5],_),_rS=jsCreateElem(toJSStr(_ry)),_rT=A(_5b,[_5h,[0,_rS],_gP,_k7,_]),_rU=jsAppendChild(_rS,_rw),_rV=jsCreateElem(toJSStr(_lj)),_rW=jsSetInnerText(_rV,toJSStr(E(_hk))),_rX=jsAppendChild(_rV,_rS),_rY=(function(_rZ,_){while(1){var _s0=E(_rZ);if(!_s0[0]){return _5a;}else{var _s1=_h4(_s0[1],_),_s2=jsAppendChild(E(_s1)[1],_rS);_rZ=_s0[2];continue;}}})(_qO[8],_),_s3=E(_li),_s4=jsFind(toJSStr(_s3)),_s5=E(_s4);if(!_s5[0]){var _s6=_jr(_hj,_),_s7=rMV(_lB),_s8=E(_s7)[3],_s9=function(_){var _sa=E(_s8);switch(_sa[0]){case 2:if(!E(E(_sa[1])[1])){return _5a;}else{var _sb=jsSetTimeout(150,E(_mc)[1]);return _5a;}break;case 3:return _5a;default:var _sc=jsSetTimeout(150,E(_mc)[1]);return _5a;}},_sd=function(_){var _se=E(_s8);if(_se[0]==2){if(!E(E(_se[1])[1])){var _sf=_md(_);return _s9(_);}else{var _sg=_lU(_);return _s9(_);}}else{var _sh=_lU(_);return _s9(_);}};switch(E(_s8)[0]){case 2:return _sd(_);case 3:var _si=_md(_);return _s9(_);default:return _sd(_);}}else{var _sj=E(_s5[1]),_sk=_sj[1],_sl=jsClearChildren(_sk),_sm=jsCreateElem(toJSStr(_s3)),_sn=jsAppendChild(_sm,_sk),_so=jsCreateElem(toJSStr(E(_lh))),_sp=jsSetInnerText(_so,toJSStr(E(_kj))),_sq=jsAppendChild(_so,_sm),_sr=E(_lf),_ss=jsCreateElem(toJSStr(_sr)),_st=jsAppendChild(_ss,_sm),_su=function(_sv,_){var _sw=jsCreateElem(toJSStr(E(_lg))),_sx=function(_sy){var _sz=jsSetInnerText(_sw,toJSStr(_sy)),_sA=jsAppendChild(_sw,_ss);return _5a;},_sB=E(_sv);return _sB==0?_sx(E(_ki)):_sx(unAppCStr("Player ",new T(function(){return _16(0,_sB,_1);})));},_sC=function(_){var _sD=_bq(_qV,0)-1|0,_sE=function(_){var _sF=function(_){var _sG=rMV(_lB),_sH=E(_sG)[3],_sI=function(_){var _sJ=E(_sH);switch(_sJ[0]){case 2:if(!E(E(_sJ[1])[1])){return _5a;}else{var _sK=jsSetTimeout(150,E(_mc)[1]);return _5a;}break;case 3:return _5a;default:var _sL=jsSetTimeout(150,E(_mc)[1]);return _5a;}},_sM=function(_){var _sN=E(_sH);if(_sN[0]==2){if(!E(E(_sN[1])[1])){var _sO=_md(_);return _sI(_);}else{var _sP=_lU(_);return _sI(_);}}else{var _sQ=_lU(_);return _sI(_);}};switch(E(_sH)[0]){case 2:return _sM(_);case 3:var _sR=_md(_);return _sI(_);default:return _sM(_);}},_sS=function(_){var _sT=A(_bB,[_5h,_sj,_kf,_kh,_]),_sU=A(_bv,[_5h,_sj,_gS,_kg,_]);return _sF(_);};switch(E(_qQ)[0]){case 2:return _sS(_);case 3:var _sV=A(_bB,[_5h,_sj,_kf,_ke,_]),_sW=A(_bv,[_5h,_sj,_gS,_kd,_]);return _sF(_);default:return _sS(_);}};if(0<=_sD){var _sX=new T(function(){var _sY=E(_qP);switch(_sY[0]){case 0:return E(_lc);case 1:return E(_ld);default:return _1h(0,_sY[1]-1|0);}}),_sZ=jsCreateElem(toJSStr(_sr)),_t0=jsAppendChild(_sZ,_sm),_t1=function(_){var _t2=E(_sD);if(!_t2){return _sE(_);}else{var _t3=(function(_t4,_){while(1){var _t5=(function(_t6,_){var _t7=jsCreateElem(toJSStr(_sr)),_t8=jsAppendChild(_t7,_sm),_t9=E(_sX);if(!_t9[0]){if(_t6!=_t2){var _ta=_t6+1|0;_t4=_ta;return null;}else{return _5a;}}else{var _tb=E(_le),_tc=jsCreateElem(toJSStr(_tb));if(_t6>=0){var _td=jsSetInnerText(_tc,toJSStr(_16(0,_1D(_b5(_qP,E(_t9[1])[1])[3],_t6)[1],_1))),_te=jsAppendChild(_tc,_t7),_tf=(function(_tg,_){while(1){var _th=E(_tg);if(!_th[0]){return _5a;}else{var _ti=jsCreateElem(toJSStr(_tb)),_tj=jsSetInnerText(_ti,toJSStr(_16(0,_1D(_b5(_qP,E(_th[1])[1])[3],_t6)[1],_1))),_tk=jsAppendChild(_ti,_t7);_tg=_th[2];continue;}}})(_t9[2],_);if(_t6!=_t2){var _ta=_t6+1|0;_t4=_ta;return null;}else{return _5a;}}else{return E(_1A);}}})(_t4,_);if(_t5!=null){return _t5;}}})(1,_);return _sE(_);}},_tl=E(_sX);if(!_tl[0]){return _t1(_);}else{var _tm=E(_le),_tn=jsCreateElem(toJSStr(_tm)),_to=jsSetInnerText(_tn,toJSStr(_16(0,_1D(_b5(_qP,E(_tl[1])[1])[3],0)[1],_1))),_tp=jsAppendChild(_tn,_sZ),_tq=(function(_tr,_){while(1){var _ts=E(_tr);if(!_ts[0]){return _5a;}else{var _tt=jsCreateElem(toJSStr(_tm)),_tu=jsSetInnerText(_tt,toJSStr(_16(0,_1D(_b5(_qP,E(_ts[1])[1])[3],0)[1],_1))),_tv=jsAppendChild(_tt,_sZ);_tr=_ts[2];continue;}}})(_tl[2],_);return _t1(_);}}else{return _sE(_);}},_tw=E(_qP);switch(_tw[0]){case 0:return _sC(_);case 1:var _tx=(function(_ty,_){while(1){var _tz=_su(_ty,_),_tA=E(_ty);if(!_tA){return _5a;}else{_ty=_tA+1|0;continue;}}})(0,_);return _sC(_);default:var _tB=_tw[1]-1|0;if(0<=_tB){var _tC=(function(_tD,_){while(1){var _tE=_su(_tD,_);if(_tD!=_tB){var _tF=_tD+1|0;_tD=_tF;continue;}else{return _5a;}}})(0,_);return _sC(_);}else{return _sC(_);}}}}},_tG=E(_qP);if(_tG[0]==2){var _tH=_tG[1]-1|0;if(1<=_tH){var _tI=(function(_tJ,_){while(1){var _tK=(function(_tL,_){var _tM=E(_kw),_tN=jsCreateElem(toJSStr(_tM)),_tO=jsAppendChild(_tN,_re),_tP=A(_5b,[_5h,[0,_tN],_gP,new T(function(){return unAppCStr("player-",new T(function(){return _16(0,_tL,_1);}));}),_]),_tQ=jsCreateElem(toJSStr(_lm)),_tR=jsSetInnerText(_tQ,toJSStr(unAppCStr("Player ",new T(function(){return _W(_16(0,_tL,_1),_km);})))),_tS=function(_){var _tT=jsCreateElem(toJSStr(_tM)),_tU=jsAppendChild(_tT,_tN),_tV=A(_5b,[_5h,[0,_tT],_gP,_kb,_]),_tW=(function(_tX,_){while(1){var _tY=E(_tX);if(!_tY[0]){return _5a;}else{var _tZ=_h4(_dK,_),_u0=jsAppendChild(E(_tZ)[1],_tT);_tX=_tY[2];continue;}}})(_b5(_tG,_tL)[1],_),_u1=jsCreateElem(toJSStr(_tM)),_u2=jsAppendChild(_u1,_tN),_u3=A(_5b,[_5h,[0,_u1],_gP,_k8,_]);return (function(_u4,_){while(1){var _u5=E(_u4);if(!_u5[0]){return _5a;}else{var _u6=_h4(_u5[1],_),_u7=jsAppendChild(E(_u6)[1],_u1);_u4=_u5[2];continue;}}})(_b5(_tG,_tL)[2],_);},_u8=E(_qQ);if(_u8[0]==2){if(_tL!=E(_u8[1])[1]){var _u9=jsAppendChild(_tQ,_tN),_ua=_tS(_);if(_tL!=_tH){var _ub=_tL+1|0;_tJ=_ub;return null;}else{return _5a;}}else{var _uc=_5k(_tN,_gP,_kc,_),_ud=jsAppendChild(_tQ,_tN),_ue=_tS(_);if(_tL!=_tH){var _ub=_tL+1|0;_tJ=_ub;return null;}else{return _5a;}}}else{var _uf=jsAppendChild(_tQ,_tN),_ug=_tS(_);if(_tL!=_tH){var _ub=_tL+1|0;_tJ=_ub;return null;}else{return _5a;}}})(_tJ,_);if(_tK!=null){return _tK;}}})(1,_);return _rg(_);}else{return _rg(_);}}else{return _rg(_);}}};switch(E(_qQ)[0]){case 2:return _qR(E(_ko));case 3:return _qR(E(_kp));default:return _qR(E(_ko));}}},_uh=function(_){var _ui=function(_){if(E(_lP)[0]==2){var _uj=function(_){var _uk=rMV(_lB),_=wMV(_lB,new T(function(){var _ul=E(_uk),_um=_ul[8];return [0,new T(function(){return _2k(function(_un){var _uo=E(_un),_up=_uo[2];return [0,_uo[1],_up,new T(function(){return _W(_uo[3],[1,new T(function(){return [0,_bO(_8u(function(_uq){var _ur=_jH(_3n,new T(function(){return _hr(_uq);}),new T(function(){return _2Y(_dH,_1,_hF(_um));}));return _ur[0]==0?E(_4k):E(_ur[1]);},_up),0)];}),_1]);})];},_ul[1]);}),_ul[2],_V,_ul[4],_ul[5],_ul[6],_ul[7],_um,_ul[9]];}));return _5a;},_us=_3t(_l7,_7,_2k(_la,_lO));switch(_us[0]){case 0:return _5a;case 1:return _uj(_);default:return E(_us[1])==0?_5a:_uj(_);}}else{return _5a;}},_ut=E(_lP);if(_ut[0]==2){if(!_21(_3j,_lQ,_1)){var _uu=E(_lQ);if(!_uu[0]){return E(_hq);}else{var _uv=E(_uu[1]);if(_uv[0]==2){var _uw=E(_uv[1]);if(!_uw[0]){return E(_hq);}else{var _ux=function(_uy){if(E(_uy)==8){var _=wMV(_lB,[0,_lO,_lN[2],[2,new T(function(){return [0,_fC(E(_ut[1])[1]+3|0,4)];})],_lN[4],_lN[5],_lN[6],_lN[7],_lN[8],_uu]),_uz=_8C(_lB,_);return _ui(_);}else{return _ui(_);}},_uA=E(_uw[1]);switch(_uA[0]){case 0:return _ux(E(_uA[2])[1]);case 1:return _ux(0);default:return _ux(-1);}}}else{return _ui(_);}}}else{return _ui(_);}}else{return _ui(_);}};if(E(_lP)[0]==2){if(!_21(_3j,_d2(3,_lQ),_i7)){var _uB=_uh(_);return _lR(_);}else{var _uC=_8C(_lB,_),_uD=_uh(_);return _lR(_);}}else{var _uE=_uh(_);return _lR(_);}};switch(E(_lD[3])[0]){case 0:var _uF=_gn(_lF,_),_=wMV(_lB,[0,_lE,_lD[2],_dL,_uF,_lG,_lH,_lI,_lJ,_lK]);return _lL(_);case 1:var _uG=_gn(_lF,_),_uH=new T(function(){return _jv(_lE,_lv(_kt,new T(function(){return _lq(function(_uI){var _uJ=E(_uI);return _uJ[0]==0?[0]:[1,new T(function(){var _uK=E(new T(function(){var _uL=E(_lE);switch(_uL[0]){case 0:var _uM=_bq(_uG,0);return E(_eT);case 1:return [0,_i2(_bq(_uG,0),1)+1|0];default:var _uN=_bq(_uG,0),_uO=E(_uL[1]);switch(_uO){case -1:var _uP=E(_uN);return _uP==(-2147483648)?E(_lo):[0,_i2(_uP,-1)+1|0];case 0:return E(_eT);default:return [0,_i2(_uN,_uO)+1|0];}}}))[1];if(_uK>=0){var _uQ=_bH(_uK,_uJ);return [0,_uQ[1],_uQ[2]];}else{return [0,_1,_uJ];}})];},_uG);})));}),_uR=new T(function(){var _uS=A(_2Y,[_jT,_jt,_2k(_kr,_uH),_38]);return _uS[0]==0?E(_0):E(_uS[1]);}),_=wMV(_lB,[0,_uH,_uR,[2,_uR],_1,_lG,_lH,_lI,_lJ,_lK]);return _lL(_);default:return _lL(_);}},_uT=function(_){var _uU=nMV(_1y);return _lA(_uU,_);},_uV=function(_){return _uT(_);};
var hasteMain = function() {A(_uV, [0]);};window.onload = hasteMain;