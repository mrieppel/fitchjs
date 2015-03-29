// SI/TI RULE CHECKING FUNCTIONS (LSL ONLY)
// ========================================

// Main SI/TI checking function
function ckSI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line(s) '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=(l.seq.length-1)) {
		throw flag+'The rule is being applied to an inappropriate number of lines.';
	}
	if(l.seq.length==1) {
		var x = match(parse(l.seq[0]),l.tr);
		if(!x[0]) {nope();}
		if(clash(x[1])) {nope();}
	}
	if(l.seq.length==2) {
		var x = match(parse(l.seq[0]),PROOF[l.lin[0]-1].tr);
		if(!x[0]) {nope();}
		var y = match(parse(l.seq[1]),l.tr);
		if(!y[0]) {nope();}
		if(clash(x[1].concat(y[1]))) {nope();}
	}
	if(l.seq.length==3) {
		var x = match(parse(l.seq[0]),PROOF[l.lin[0]-1].tr);
		if(!x[0]) {nope();}
		var y = match(parse(l.seq[1]),PROOF[l.lin[1]-1].tr);
		if(!y[0]) {nope();}
		var z = match(parse(l.seq[2]),l.tr);
		if(!z[0]) {nope();}
		if(clash(x[1].concat(y[1],z[1]))) {nope();}
	}
	
	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
	function nope() {
		throw flag+'The formula being derived does not follow by '+gRul(l.rul)+'.';
	}
}

// String -> [String]
// Extracts the SI sequent (as an array) from the 'value' attribute of the selected 
// rule (see the html <option> elements).  E.g. from 'SI(MT):(A>B),~B,~A' will return 
// ['(A>B)','~B','~A']
function getSeq(s) {
	var o = '';
	var i = 0;
	if(s.indexOf(':')<0) {return [];}
	while(s[i]!=':') {i++;}
	o = s.substr(i+1);
	o = o.replace(/ /g,'');
	return o.split(',');
}

// String -> String
// Extracts the SI rule name (as string) from the 'value' attribute of the selected
// rule.  E.g. from 'SI(MT):(A>B),~B,~A' will return 'SI(MT)'.
function getSeqHead(s) {
	var o = '';
	var i = 0;
	if(s.indexOf(':')<0) {return s;}
	while(s[i]!=':') {i++;}
	return s.substr(0,i);
}

// (Tree,Tree) -> [Boolean,Dictionary]
// Takes two trees,t1 and t2, where t1 is a "template" and t2 is to be matched
// against that template.  Returns an array with the first element 'true' if
// t2 matches the template, and the second element a "dictionary" of the matches.
// Returns an array with the first element 'false' if t2 doesn't match the template.
// E.g. if the template is "(A&B)", it will match any t2 that is a conjunction, and 
// give a dictionary with 'A' assigned to the first conjunct of t2 and 'B' assigned
// to the second conjunct of t2.  So match(parse("(A&B)"),parse("((F>G)&D)")) will
// return [true,[['A','(F>G)'],['B','D']]].
function match(t1,t2) {
	var a = ['A','B','C'];
	var out = [];
	function foo(x,y) {
		for(var i=0;i<x.length;i++) {
			if(x[i] instanceof Array && y[i] instanceof Array) {
				if(!foo(x[i],y[i])) {return false;}
			} else if(a.indexOf(x[i])>=0) {
				out.push([a[a.indexOf(x[i])],unparse(y)]);
			} else if (x[i]!=y[i]) {return false;}
		}
		return true;
	}
	var t = foo(t1,t2);
	if(t) {t=!clash(out);}
	return t ? [t,out] : [t,[]];
}

// Dictionary -> Boolean
// Checks a "dictionary" element of the match function to see if there are any clashes,
// where a clash occurs if the dictionary matches a certain template variable to different
// strings.  If there is a clash it returns 'true', if not it returns 'false'. E.g. 
// [['A','F>G'],['A','D']] contains a clash, but [['A','F>G'],['A','F>G']] does not.
function clash(ar) {
	var a1 = ar[0];
	ar = ar.slice(1);
	if(ar.length==0) {return false;}
	for(var i=0;i<ar.length;i++) {
		if(ar[i][0]==a1[0] && ar[i][1]!=a1[1]) {
			return true;
		}
	}
	return clash(ar);
}
