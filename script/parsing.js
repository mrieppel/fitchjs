// FORMULA PARSING CODE
//====================

/* THE GRAMMAR
S ::= Q S | U S | '(' S B S ')' | A
Q ::= '(A' V ')' | '(E' V ')'
U ::= '~'
B ::= '&' | 'v' | '>' | '<>'
A ::= '#' | T=T | P | P T | P T T | P T T T ...
P ::= 'A' | 'B' | 'C' | 'D' | ...
T ::= C | V
C :: = 'a' | 'b' | 'c' | 'd'
V :: = 'w' | 'x' | 'y' | 'z' 
*/

// Tree -> String		
// Takes a parse tree (as output by the parse function below) and returns the 
// string it is a parse tree of.
function unparse(ar) {
	if(ar.length==2 && (isQ(ar[0]) || isU(ar[0]))) {
		return ar[0] + unparse(ar[1]);
	}
	if(ar.length==3 && isB(ar[1])) {
		return '('+unparse(ar[0])+ar[1]+unparse(ar[2])+')';
	}
	else {
		return ar.join('');
	}
}

// String -> Tree
// Takes a string and if it's a wff, returns a parse tree of the string, otherwise
// returns an empty array.
function parse(s) {
	if(s=='') {return [];}
	var s1 = [];
	var s2 = [];
	if(isQ(s)) {
		s1 = parse(s.substring(4));
		return s1.length ? [s.substring(0,4),s1] : [];
	}
	if(isU(s[0])) {
		s1 = parse(s.substring(1));
		return s1.length ? [s[0],s1] : [];
	}
	if(s[0] =='(' && s[s.length-1]==')') {
		var a = gSub(s);
		if(a.indexOf(undefined)>=0 || a.indexOf('')>=0) {
			return [];
		} else {
			s1 = parse(a[0]);
			s2 = parse(a[2]);
			if(s1.length && s2.length) {
				return [s1,a[1],s2];
			} else {return [];}
		}
	}
	else {return isA(s) ? s.split('') : []}
}

// String -> Bool
// Determines if s is an atomic wff
function isA(s) {
	var pr = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
	if(s.length==1 && isAbs(s)) {return true;}
	if(s.length==3 && isT(s[0]) && s[1]=='=' && isT(s[2])) {
		return true;
	}
	if(pr.indexOf(s[0])>=0) {
	 	if(s.length==1) {
	 		return true;
	 	} else {
	 		for(var i=1;i<s.length;i++) {
	 			if(!isT(s[i])) {
	 				return false;
	 			}
	 		}
	 		return true;
	 	}
		
	} else {return false;}
}

// String -> Bool
// Determines if s is the absurdity
function isAbs(s) {
	var abs = ['#','\u22A5']
	return abs.indexOf(s)>=0;
}
// String -> Bool
// Determines if s begins with a quantifier, e.g. 'Ez(...)'
function isQ(s) {
	var q = ['E','A','\u2203','\u2200'];
	if(s[0]=='(' && q.indexOf(s[1])>=0 && isV(s[2]) && s[3]==')') {
		return true;
	} else {return false;}
}

// String -> Bool
// Determines if s begins with a unary connective
function isU(s) {
	var u = ['~','\u00AC'];
	for(var i=0;i<u.length;i++) {
		if(s.indexOf(u[i])==0) {return true;}
	}
	return false;
}

// String -> [String]
// takes a string beginning with '(' and ending with ')', and determines if there is a
// binary connective enclosed only by the outermost parentheses.  If so, returns an array
// with the string to the left and the string to the right of the binary connective; 
// otherwise returns an array of three undefined's.
function gSub(s) {
	var stk = [];
	var l = 0;
	for(var i=0;i<s.length;i++) {
		if(s[i]=='(') {
			stk.push('(');
		} else if(s[i]==')' && stk.length>0) {
			stk.pop();
		} else if(stk.length==1 && (l = isB(s.substring(i)))>0) {
			return [s.substring(1,i),s.substring(i,i+l),s.substring(i+l,s.length-1)];
		}	
	}
	return [undefined,undefined,undefined];
}

// String -> Int
// takes a string and determines if it begins with a binary connective.  If so, returns
// the length of the connective, otherwise returns 0.
function isB(s) {
	var bc = ['&','v','>','<>','\u2227','\u2228','\u2283','\u2261'];
	for(var i=0;i<bc.length;i++) {
		if(s.indexOf(bc[i]) == 0) {
			return bc[i].length;
		}
	}
	return 0;
}

// Char -> Bool
// Determines if c is a term
function isT(c) {
	return (isC(c) || isV(c));
}

// Char -> Bool
// Determines if c is a variable.  NOTE: /[a-z]/.test(undefined) gives true!!!
function isV(c) {
	var cn = 'abcdefghijklmnopqrstuwxyz';
	return cn.indexOf(c)>=0;
}

// Char -> Bool
// Determines if c is a constant
function isC(c) {
	var cn = 'abcdefghijklmnopqrstuwxyz';
	return cn.indexOf(c)>=0;
}

// RICHARDIFY THE FORMULA
//=======================

// String -> String
// Takes a formula and performs unicode substitutions.  Also works "in reverse".
function richardify(s) {
	if(s=="") {
		return s;
	} else if(isQ(s)) {
		return s[0]+ptou(s[1])+s[2]+s[3]+richardify(s.substring(4,s.length))	
	} else if(isU(s[0])) {
		return ptou(s[0])+richardify(s.substring(1,s.length));
	} else if(s[0] =='(' && s[s.length-1]==')') {
		var a = gSub(s);
		return '('+richardify(a[0])+ptou(a[1])+richardify(a[2])+')';
	} else if(isAbs(s)) {return ptou(s);} else {return s;}
}

function latexify(s) {
	var out = '';
	var test = '';
	for(var i=0;i<s.length;i++) {
		test = utox(s[i]);
		if(test!=s[i]) {test += ' ';}
		out += test;
	}
	return out;
}

// String -> String
// Returns unicode for rules.  Also works "in reverse".
function gRul(s) {
	var out = '';
	var c = '';
	for(var i=0;i<s.length;i++) {
		if(s[i]=='<') {
			c = ptou(s[i]+s[i+1]);
			i++;
		} else if(s[i]=='E' || s[i]=='A') {
			c = (i==0 && s.length==2) ? ptou(s[i]) : s[i];
		} else {
			c = ptou(s[i]);
		}
		out += c;
	}
	return out;
}

// switches between 'plain' symbols and unicode, both directions
function ptou(s) {
	switch(s) {
		//case '~': return '\u00AC';
		//case '\u00AC' : return '~';
		//case '&' : return '\u2227';
		//case '\u2227' : return '&';
		case 'v' : return '\u2228';
		case '\u2228' : return 'v';
		case '>': return '\u2283';
		case '\u2283' : return '>';
		case '<>': return '\u2261';
		case '\u2261' : return '<>';
		case '#': return '\u22A5';
		case '\u22A5' : return '#';
		case 'A': return '\u2200';
		case '\u2200': return 'A';
		case 'E': return '\u2203';
		case '\u2203' : return 'E';
		default: return s;
	}
}

// replaces unicode with latex
function utox(c) {
	switch(c) {
		case '~' : return '\\sim';
		case '&' : return '\\&';
		case '\u2228' : return '\\lor';
		case '\u2192' : return '\\supset';
		case '\u2194' : return '\\equiv';
		case '\u22A5' : return '\\bot';
		case '\u2200': return '\\forall';
		case '\u2203' : return '\\exists';
		default: return c;
	}
}

function padBCs(str) {
	var out = '';
	var b = 0;
	for(var i=0;i<str.length;i++) {
		b = isB(str.substring(i));
		if(b==1) {
			out = out+' '+str[i]+' ';
		} else if(b==2) {
			out = out+' '+str[i]+str[i+1]+' ';
			i = i+1;
		} else {out = out+str[i];}
	}
	return out;
}