// VARIOUS HELPER FUNCTIONS TO CHECK THE USER INPUT
//=================================================

// Checks the syntax of the depth, tree, and rule lines
function ckSyn(l) {
	if(l.rul=='--Select--') {
		throw 'ERROR: select a rule.';
	}
	if(l.tr.length==0 && l.rul!='Flag') {
		throw 'ERROR: Formula is malformed.';
	}
	if(l.rul=='Flag' && !isT(l.frm)) {
		throw 'ERROR: Flagged term is malformed.'
	}
	var x = badchar(l.frm);
	if(x>=0) {
		throw 'ERROR: the formula you entered contains the unrecognized character \''+l.frm[x]+'\'.  See the syntax guide under the Reference tab.';
	}
	if(!(l.lin=='') && !ckc(l.lin)) {
		throw 'ERROR: Rule lines are malformed';
	}
}

// Takes the input line and dispatches it to the appropriate rule checking function.
// If the second parameter n is 0, the extra line attributes (sig, avl etc.) are 
// filled in by the relevant rule checking function, and if n is 1 the current 
// settings of the attributes are used (if line is being checked rather than entered)
function ckRest(l,n) {
	var x = 0;
	if((x = oob(l.lin,l.cnt))>0) {
		throw 'ERROR: Rule line '+x+ ' is out of bounds. Rules must be applied to preceding lines.';
	}
 	if(l.rul=='Premise') {return ckPR(l,n);}
 	else if(l.rul=='Assumption') {return ckAS(l,n);}
	else if(l.rul=='Reit') {return ckRE(l,n);}
 	else if(l.rul=='&I') {return ckCJI(l,n);}
 	else if(l.rul=='&E') {return ckCJE(l,n);}
  	else if(l.rul=='vI') {return ckDJI(l,n);}
  	else if(l.rul=='vE') {return ckDJE(l,n);}
  	else if(l.rul=='>I') {return ckCNI(l,n);}
  	else if(l.rul=='>E') {return ckCNE(l,n);}
  	else if(l.rul=='<>I') {return ckBCI(l,n);}
  	else if(l.rul=='<>E') {return ckBCE(l,n);}
  	else if(l.rul=='~I') {return ckNI(l,n);}
   	else if(l.rul=='~E') {return ckNE(l,n);}
   	else if(l.rul=='DN') {return ckDN(l,n);}
  	else if(l.rul=='Flag') {return ckFLG(l,n);}
  	else if(l.rul=='EI') {ckEI(l,n);}
  	else if(l.rul=='EE') {ckEE(l,n);}
  	else if(l.rul=='AI') {ckAI(l,n);}
  	else if(l.rul=='AE') {ckAE(l,n);}
 	else if(l.rul=='=I') {ckIDI(l,n);}
  	else if(l.rul=='=E') {ckIDE(l,n);}
  	else if(l.rul=='SI(QS)') {ckQS(l,n);}
  	else if(l.rul=='SI(AV)') {ckAV(l,n);}
  	else if(l.rul.indexOf('SI')==0) {ckSI(l,n);}
 	else {throw "ERROR: The rule "+l.rul+" you entered is not recognized.";}
}

// [Int] -> (Int -> Boolean)
// Out-Of-Bounds function. Takes an array of ints and an int n and returns 0 if none
// of the array elements are > n, else returns the value of the array element >n.
function oob(ar,n) {
	for(var i=0;i<ar.length;i++) {
		if(ar[i] >= n) {
			return ar[i];
		}
	}
	return 0;
}

// String -> Boolean
// Takes a string and checks if it has the form: numeral comma numeral comma ... etc.
function ckc(s) {
	var n = ['0','1','2','3','4','5','6','7','8','9'];
	var st = false;
	var c = '';
	for(var i=0;i<s.length;i++) {
		c = s[i];
		if(n.indexOf(c)>=0) {
			st=true;
		} else if(c==',' && st) {
			st = false;
		} else {return false;}
	}
	return st;
}

// [Int] -> [Int]
// Takes an array of ints and returns the array sorted from smallest to largest
function sorted(a) {
	return a.sort(function(a,b) {return a-b;});
}

// String -> [Int]
// Takes an array in the CSV format checked by ckc, and returns
// the corresponding array of ints
function mkIntArr(s) {
	if(s=='') {
		return [];
	} else {
		var a = s.split(',');
		return a.map(function(x){return parseInt(x,10);});
	}
}

// [String] -> Int
// Takes an array of strings and returns the length of its longest element.
function max(ar) {
	var n = 0;
	for(var i=0;i<ar.length;i++) {
		if(ar[i].length > n) {
			n = ar[i].length;
		}
	}
	return n;
}

// String -> Boolean
// Takes a string and checks that every char is a numeral
function isInt(s) {
	var n = ['0','1','2','3','4','5','6','7','8','9'];
	for(var i=0;i<s.length;i++) {
		if(n.indexOf(s[i])<0) {
			return false;
		}
	}
	return !(s.length==0);
}

// Array -> Array
// Takes an array and removes duplicate elements
function rmDup(a) {
	return a.filter(function(el,pos) {return a.indexOf(el)==pos;});
}

// String -> Int
// Checks if the string contains any inadmissible characters
function badchar(s) {
	var x = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz()~&<>=#';
	for(var i=0;i<s.length;i++) {
		if(x.indexOf(s[i])<0) {
			return i;
		}
	}
	return -1;
}
