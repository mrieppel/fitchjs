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
	if(!cklin(l.lin)) {
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
	var r = l.rul;
 	if(r=='Premise') {return ckPR(l,n);}
 	else if(r=='Assumption') {return ckAS(l,n);}
	else if(r=='Reit') {return ckRE(l,n);}
 	else if(r=='&I') {return ckCJI(l,n);}
 	else if(r=='&E') {return ckCJE(l,n);}
 	else if(r=='>I') {return ckCNI(l,n);}
  	else if(r=='>E') {return ckCNE(l,n);}
  	else if(r=='vI') {return ckDJI(l,n);}
  	else if(r=='vE') {return ckDJE(l,n);}
  	else if(r=='~I') {return ckNI(l,n);}
   	else if(r=='~E') {return ckNE(l,n);}
   	else if(r=='DN') {return ckDN(l,n);}
   	else if(r=='EFQ') {return ckEFQ(l,n);}
  	else if(r=='<>I') {return ckBCI(l,n);}
  	else if(r=='<>E') {return ckBCE(l,n);}
  	else if(r=='Flag') {return ckFLG(l,n);}
  	else if(r=='EI') {ckEI(l,n);}
  	else if(r=='EE') {ckEE(l,n);}
  	else if(r=='AI') {ckAI(l,n);}
  	else if(r=='AE') {ckAE(l,n);}
 	else if(r=='=I') {ckIDI(l,n);}
  	else if(r=='=E') {ckIDE(l,n);}
  	else if(r.indexOf('TI(LEM)')>0) {ckTI(l,n);}
  	else if(r.indexOf('DeM')>0||r.indexOf('Imp')>0||r.indexOf('Dist')>0) {ckSIbi(l,n);} 
  	else if(r=='SI(QS)') {ckQS(l,n);}
  	else if(r=='SI(AV)') {ckAV(l,n);}
  	else if(r.indexOf('SI')==0) {ckSI(l,n);}
 	else {throw "ERROR: The rule "+r+" you entered is not recognized.";}
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
// Takes a string and checks if it has the proper form of a line citation, e.g.
// "1,2" or "1,2-3,4-5,6"
function cklin(s) {
	if(s.length==0) {return true;}
	var n = ['0','1','2','3','4','5','6','7','8','9'];
	var st = 0;
	var c = '';
	for(var i=0;i<s.length;i++) {
		c = s[i];
		if((st==0||st==1) && n.indexOf(c)>=0) {
			st=1;
		} else if(st==1 && c=="-") {
			st=2;
		} else if ((st==2||st==3) && n.indexOf(c)>=0) {
			st=3;
		} else if((st==1 || st==3) && c==",") {
			st=0;
		} else {st=4;}
	}
	return (st==1 || st==3);
}

// Takes a line citation string (as validated by cklin()) and turns it into an array
// of ints, with subprooof citations marked by '-'; e.g. "1,2" becomes [1,2] and
// "1-2" becomes [1,"-",2];
function linArr(s) {
	if(s=="") {return [];}
	var ar = s.split(','),
		t = [],
		out = [];
		
	for(var i=0;i<ar.length;i++) {
		if(ar[i].indexOf('-')<0) {
			out.push(parseInt(ar[i]));
		} else {
			t = ar[i].split('-');
			out.push(parseInt(t[0]));
			out.push('-');
			out.push(parseInt(t[1]));
		}
	}
	return out;
}

// Takes a lin array (as produced by linArr()) and turns it back into a string
function linD(a) {
	var out = "";
	for(var i=0;i<a.length;i++) {
		if(a[i]=="-") {
			out += "-";
		} else {
			if (i==(a.length-1)) {
				out += a[i].toString();
			} else if (a[i+1]=="-") {
				out += a[i].toString();
			} else {
				out += a[i].toString()+",";
			}
		}
	}
	return out;
}

// [Int] -> [Int]
// Takes an array of ints and returns the array sorted from smallest to largest
function sorted(a) {
	return a.sort(function(a,b) {return a-b;});
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
