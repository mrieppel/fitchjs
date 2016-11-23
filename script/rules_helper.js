// HELPER FUNCTIONS FOR RULE CHECKING
// ==================================

// Fills the dth, sig, avl, and frv properties of lines with non-discharge rules
function fillND(l) {
	if(!PROOF.length) {throw "[ERROR]: cannot begin a proof using "+gRul(l.rul)+".";}
	l.sig = PROOF[l.cnt-2].sig.slice(0);
	l.dth = l.sig.length;
	l.avl = PROOF[l.cnt-2].avl.slice(0).concat(l.cnt-1);
	l.frv = freeVars(l.tr);
}

// Fills the dth, sig, avl, and frv properties of lines with discharge rules
// The arguments l and sc are the line in question and the line number of the conclusion 
// of the subproof the line is applied to (in the case of rules that appeal to two
// subproofs, pass the sc of the second subproof).
function fillD(l,sc) {
	if(!PROOF.length) {throw "[ERROR]: cannot begin a proof using "+gRul(l.rul)+".";}
	if(sc==l.cnt-1) {
		l.sig = PROOF[sc-1].sig.slice(0,PROOF[sc-1].sig.length-1);
	} else {l.sig = PROOF[l.cnt-2].sig.slice(0);}
	l.dth = l.sig.length;
	l.avl = gtAvl(l);
	l.frv = freeVars(l.tr)
}

// Line -> [Int]
// Takes a Line and return the set of lines available to that line
function gtAvl(l) {
	var out = [];
	for(var i=0;i<(PROOF.length);i++) {
		if(subset(PROOF[i].sig,l.sig)) {
			out.push(i+1);
		}
	}
	return out;
}

// Where l is a set of lines and a the set of available lines, 
// checks if all elements of l are in a.  If so returns -1,
// otherwise returns the number of the first unavailable line in l 
function areAvl(l,a) {
	for(var i=0;i<l.length;i++) {
		if(a.indexOf(l[i])<0) { return l[i];}
	}
	return -1;
}

// ([Int],[Int]) -> Bool
// Checks if s1 is a subset of s2
function subset(s1,s2) {
	if(s1.length>s2.length) {return false;}
	for(var i=0;i<s1.length;i++) {
		if(s2.indexOf(s1[i])<0) {return false;}
	}
	return true;
}

// ([Int],[Int]) -> Bool
// Takes two arrays of ints and determines if they are the same
function same(s1,s2) {
	if(s1.length!=s2.length) {return false;}
	for(var i=0;i<s1.length;i++) {
		if(s1[i]!=s2[i]) {return false;}
	}
	return true;
}

// [Int] -> [Char]
// Takes a list of line numbers and returns a list of any free variables on those lines
function frvList(l) {
	var out = [];
	for(var i=0;i<l.length;i++) {
		out = out.concat(PROOF[l[i]-1].frv);
	}
	return out;
}

// (Tree,String) -> Char
// Takes a parse tree of a quantified formula and a string to determine if the string
// is an instance of the quantified formula.  If so returns the char of the instantial
// variable/constant; if not, returns '_'.
// NOTE: if the quantifier is vacuous as in e.g. '(Ax)(Fa>Ga)' or '(Ax)P', it returns '+'
// a "throwaway" char to indicate the String is an instance but involves no 
// instantial variable
function isInst(t,s) {
	var tmp = mkTmp(t);
	var b = blockedVars(tmp);
	var stmp = unparse(tmp);
	if(stmp.length!=s.length) {return '_';};
	if(s==stmp) {return '+';} // vacuous quantifier
	var iv = s[stmp.indexOf('_')];
	if(b.indexOf(iv)>=0) {return '_';}
	return s==stmp.replace(/_/g,iv) ? iv : '_';
}

// Tree -> Tree
// Takes a parse tree of a quantified formula and returns a template for 
// creating instances (with '_' where the instantial variable/constant is to go).
// So e.g. the parse tree of "Ex(Fx>Rxz)" will return a tree of "(F_>R_z)"
function mkTmp(ar) {
	var v = ar[0][2];
	return mk(ar[1]);
	function mk(a) {
		if(a.length==2 && isQ(a[0])) {
			if(a[0][2]==v) {
				return [a[0],a[1]];
			} else {
				return [a[0],mk(a[1])];
			}
		} else if(a.length==2 && isU(a[0])) {
			return [a[0],mk(a[1])];
		} else if(a.length==3 && isB(a[1])) {
			return [mk(a[0]),a[1],mk(a[2])];
		} else {
			return replace(v,a);
		}
	}
	function replace(x,ls) {
		var out = [];
		for(var i=0;i<ls.length;i++) {
			if(ls[i]==x) {out.push('_');} else {out.push(ls[i]);}
		}
		return out;
	}
}

// Tree -> [Char]
// Takes a parse tree and returns an array containing all the free variables/constants
// in that parse tree.
function freeVars(ar) {
	function mk(a,v) {
		if(a.length==2 && isQ(a[0])) {
			v.push(a[0][2]);
			return mk(a[1],v);
		} else if(a.length==2 && isU(a[0])) {
			return mk(a[1],v);
		} else if(a.length==3 && isB(a[1])) {
			return mk(a[0],v).concat(mk(a[2],v));
		} else {
			var out = [];
			for(var i=0;i<a.length;i++) {
				if(isV(a[i]) && (v.indexOf(a[i])<0)) {
					out.push(a[i]);
				}
			}
			return out;
		}
	}
	return mk(ar,[]);
}

// (Tree,Tree,Wff) -> Boolean
// Takes the parse tree of an identity statement, the parse tree of a formula 1, and a 
// formula 2 to determine if you can get to the formula 2 from formula 1 by substituting
// one or more (not necessarily all!) occurrences of the first constant from the identity 
// with the second constant from the identity.
function checkID(id,t1,f2) {
	var f1 = unparse(t1);
	if(f2==f1) {return false;}
	if(f2.length!=f1.length) {return false;}
	var dic = [id[0],id[2]];
	function mk(a,v) {
		if(a.length==2 && isQ(a[0])) {
			v.push(a[0][2]);
			return a[0]+mk(a[1],v);
		} else if(a.length==2 && isU(a[0])) {
			return a[0]+mk(a[1],v);
		} else if(a.length==3 && isB(a[1])) {
			return '('+mk(a[0],v)+a[1]+mk(a[2],v)+')';
		} else {
			var out = '';
			for(var i=0;i<a.length;i++) {
				if(a[i]==dic[0] && v.indexOf(a[i])<0) {
					out = out+'_';
				} else {out = out+a[i];}
			}
			return out;
		}
	}
	var tmp = mk(t1,[]);
	if(tmp.indexOf('_')==(-1)) {return false;}
	for(var i=0;i<tmp.length;i++) {
		if(tmp[i]=='_') {
			if(f2[i]!=dic[0] && f2[i]!=dic[1]) {
				return false;
			}
		} else if(tmp[i]!=f2[i]) {return false;}
	}
	return true;
}

// (Tree,String,String) -> Boolean
// Takes a parse tree of a quantified formula, the quantified formula f1 of which it is
// the tree, and a formula f2, and determines if f2 is an alphabetic variant (AV) of f1.
// FOR SI(AV)
function isAV(tree,f1,f2) {
	if(f1.length!=f2.length) {return false;}
	var avlst = mkAVList(tree);
	var v = '';
	for(var i=0;i<avlst.length;i++) {
		v = f2[avlst[i][1].indexOf('_')];
		if(f2==avlst[i][1].replace(/_/g,v) && avlst[i][0].indexOf(v)<0) {
			return true;
		}
	}
	return false;
}

// Tree -> [[Char],String]
// Takes a tree and returns a list of all the AV templates for the tree (i.e. templates 
// for creating alphabetic variants of the formula encoded by the tree).  Each AV 
// template is given as a pair, the first member of which is an array of "blocked 
// variables" (cannot be used to create AV's on pain of unwanted capture), and the second
// member of which is a string version of the actual AV template.
// FOR SI(AV)
function mkAVList(tree) {
	var loc = getQLoc(tree);
	var out = [];
	var x = '';
	var b = [];
	for(var i=0;i<loc.length;i++) {
		x = mkAVtmp(getTreeAt(tree,loc[i]));
		b = blockedVars(x[1]).concat(freeVars(x[1]));
		x = insertTmp(tree,strAVtmp(x),loc[i]);
		out.push([b,x]);
	}
	return out;
}

// Tree -> [[Int]]
// Takes a parse tree and returns an array of the "locations" of the quantified
// sub formulas in the tree (locations themselves being arrays of ints).
// FOR SI(AV)
function getQLoc(tree) {
	var loc = [];
	gt(tree,[]);
	return loc;
	function gt(a,y) {
		if(a.length==2 && isQ(a[0])) {
			loc.push(y.slice(0));
			y.push(1);
			gt(a[1],y.slice(0));
		} else if(a.length==2 && isU(a[0])) {
			y.push(1);
			gt(a[1],y.slice(0));
		} else if(a.length==3 && isB(a[1])) {
			y.push(0);
			gt(a[0],y.slice(0));
			y.pop();
			y.push(2);
			gt(a[2],y.slice(0));
		}
	}
}

// Tree -> Tree
// Takes a tree of a quantified formula and returns an AV template for that tree, itself
// a tree.
// FOR SI(AV)
function mkAVtmp(tree) {
	return ['('+tree[0][1]+'_'+')',mkTmp(tree)];
}

// Tree -> String
// Takes an AV template and creates a string version of it.
// FOR SI(AV)
function strAVtmp(avtmp) {
	return avtmp[0]+unparse(avtmp[1]);
}

// ([Int],Tree) -> Tree
// Takes a "location" (output of getQLoc) and a tree and returns the subtree at
// the location in question.
// FOR SI(AV)
function getTreeAt(tree,loc) {
	for(var i=0;i<loc.length;i++) {
		tree = tree[loc[i]];
	}
	return tree;
}

// Tree -> [Char]
// Takes an instance template, generated by either mkTmp or mkAVtmp, and returns a list
// of the variables that can't be used to create instances, on pain of unwanted capture
// by some quantifier further down the tree.
// NOTE: this function expects the "complement" of a quantifier, i.e. the element at 
// tree[1] of the parse tree of a quantified formula, with the quantifier left off. 
// So when calling this with an AV  template, you have to actually pass 
// just the element at tmp[1] of the AV template.
function blockedVars(tmp) {
	blocked = [];
	gt(tmp);
	return blocked;
	function gt(t) {
		if(t.length==2&&isQ(t[0])) {
			if(hasblank(t[1])) {
				blocked.push(t[0][2]);
			}
		} else if(t.length==2&&isU(t[0])) {
			gt(t[1]);
		} else if(t.length==3&&isB(t[1])) {
			gt(t[0]);
			gt(t[2]);
		}
	}
	function hasblank(a) {
		test = false;
		for(var i=0;i<a.length;i++) {
			if(a[i] instanceof Array) {
				test = test || hasblank(a[i]);
			} else {
				test = test || a[i]=='_';
			}
		}
		return test;
	}
}

// (Tree,String,[Int]) -> String
// Takes a parse tree, a string version of an AV template (output of strAVtmp), and a 
// location, and returns the formula that you get by taking the formula represented by 
// the parse tree and replacing the subformula at the given location with the strAVtmp.
// FOR SI(AV)
function insertTmp(tree,savtmp,loc) {
	return go(tree,[])
	function go(ar,l) {
		if(smLoc(l,loc)) {return savtmp;}
		if(ar.length==2 && (isQ(ar[0]) || isU(ar[0]))) {
			return ar[0]+go(ar[1],l.concat([1]));
		}
		if(ar.length==3 && isB(ar[1])) {
			return '('+go(ar[0],l.concat([0]))+ar[1]+go(ar[2],l.concat([2]))+')';
		}
		else {
			return ar.join('');
		}
	}
	function smLoc(l1,l2) {
		if(l1.length!=l2.length) {return false;}
		for(var i=0;i<l1.length;i++) {
			if(l1[i]!=l2[i]) {return false;}
		}
		return true;
	}	
}

// takes a subproof signature and returns the line number of the last line in the 
// PROOF with that signature
function lastline(sig) {
	var l = -1;
	for(var i=PROOF.length-1;i>=0;i--) {
		if(same(sig,PROOF[i].sig)) {
			return i+1;
		}
	}
	return l;
}
