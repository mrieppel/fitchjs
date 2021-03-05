/*
README:
======

The function Line(..) immediately below shows the attributes Line objects are expected to have.  Below that are global variables that hold the proof, conclusion aimed for, and sub-goal lines the user enters.

Internally, the program uses the "plain" notation, e.g. '>' and '<>', rather than the unicode variants.  Unicode variants are used (i) when writing proof lines to the drv sig, (ii) when exporting the proof (if the user has selected "pretty print"), and (iii) for parts of error messages written to the error console.  Proofs can be imported in plain notation.  The transformations between unicode and plain notation are done via the functions richardify() and gRul().  The parser can parse formulas in either notation, but again, the "internals" of the program expect to encounter formulas in the plain notation.

NOTE 3.2.18: internally, the program uses the terminology of "SI/TI" rules ("Sequent/Theorem Introduction") for what in the user interface are called "Derived Rules."
*/




// PROOF LINE CONSTRUCTOR AND PROOF ARRAY
// ======================================


function Line(cnt,frm,tr,rul,seq,lin,sig,dth,avl,frv) {
	this.cnt = cnt; // holds line count as int
	this.frm = frm; // holds formula as string
	this.tr = tr; // holds a parse tree of the formula
	this.rul = rul; // holds the rule as string
	this.seq = seq; // holds sequents in case of an SI rule
	this.lin = lin; // holds rule lines as an array (see linArr())

	// values below get initialized during validation
	this.sig = sig; // holds line signature as array of ints (each subproof has a signature, and lines in the same subproof share a signature)
	this.dth = dth; // holds line depth as int (NB dth = sig.length)
	this.avl = avl; // holds the available lines (NB avl = [lines whose sig is a subset of this line's sig])
	this.frv = frv; // hold free variables as a char array
}

var PROOF = []; // array to hold proof lines
var CONCLUSION = []; // array to hold conclusion of proof
var GOALS = []; // array to hold goal formulas


// FUNCTIONS FOR THE USER INTERFACE
//=================================

// Sets up the proof with user entered premises and conclusion
function setup_proof() {
	var premises = document.getElementById('premises').value.replace(/ /g,'');
	premises = premises=='' ? [] : premises.split(',');
	var conclusion = document.getElementById('conclusion').value.replace(/ /g,'');
	errmess([1],''); // clear error console

	try{
		conclusion = check_goal(conclusion);
		CONCLUSION.push(conclusion);
	} catch(err) {
		clearall();
		return errmess([0],'ERROR: conclusion is not well formed.');
	}

	for(var i=0;i<premises.length;i++) {
		try{
			var l = new Line((i+1).toString(),premises[i],parse(premises[i]),'Premise',[],[]);
			validate_line(l);
			PROOF.push(l);
		} catch(err) {
			clearall();
			return errmess([0],err);
		}
	}
	errmess([3],'');
	disp('app');
	draw_conclusion();
	draw();
}

// Checks and appends line user is attempting to enter
function append_line() {
	var c = PROOF.length+1;
	var f = document.getElementById('frm').value.replace(/ /g,'');
	var t = parse(f);
	var r = document.getElementById('rul').value;
	var s = [];
	var l = document.getElementById('lin').value.replace(/ /g,'');
	if(r=='SI/TI') {
		r = document.getElementById('siti').value;
		s = getSeq(r);
		r = getSeqHead(r);
	}
	var l = new Line(c,f,t,r,s,l);

	if(l.rul=='Assumption') {
		l.sig = document.getElementById('dth').value=="Plus 1" ? '+' : '-';
	}
	try{validate_line(l);} catch(err) {return errmess([0],err);}
	PROOF.push(l);
	clear_app();
	draw();
	checkifdone();
}

// Checks the information of the line the user is attempting to append
function validate_line(l) {
	if(l.tr.length==0&&l.rul!='Flag') {
		l.frm = '('+l.frm+')';
		l.tr = parse(l.frm);
	}
	ckSyn(l);
	l.lin = linArr(l.lin);
	ckRest(l,0);
}

// Clears the last line of a proof
function clrlast() {
	if(PROOF.length==0 || PROOF[PROOF.length-1].rul == "Premise") {
		return errmess([0],"ERROR: No lines to delete.");
	} else {
		PROOF.pop();
		draw();
	}
	errmess([1],'');
}

// clear the input fields in the appt table
function clear_app() {
	document.getElementById('dth').value = 'Plus 1';
	document.getElementById('frm').value = '';
	document.getElementById('rul').value = '--Select--';
	document.getElementById('lin').value = '';
	document.getElementById('premises').value = '';
	document.getElementById('conclusion').value = '';
	show('rul');
}

// clear the gfrm input field
function clear_gfrm() {
	document.getElementById('gfrm').value = '';
}


// checks goal formula and returns validated formula
function check_goal(f) {
	var t = parse(f);

	if(t.length==0) {
		f = '('+f+')';
		t = parse(f);
		if(t.length==0) {
			throw "ERROR: goal formula is not well formed.";
		}
	}
	return f;
}

// inserts a goal formula into GOALS and draw to gls svg
function insert_goal() {
	var f = document.getElementById('gfrm').value.replace(/ /g,'');
	try{f = check_goal(f);} catch(err) {return errmess([0],err);}
	GOALS.unshift(f);
	clear_gfrm();
	draw_goals();
}

// Removes the last entered goal formula
function delete_goal() {
	if(!GOALS.length) {
		errmess([0],"ERROR: No goals to delete.");
		return;
	} else {
		GOALS.shift();
		draw_goals();
	}
	errmess([1],'');
}


// Checks the whole proof.  Takes a parameter f; if f==1, returns the error message,
// if f==undefined, prints message to error div
function ckproof(f) {
	var reply = '';
	if(PROOF.length==0) {
		reply = 'ERROR: No proof to check';
		return f==1 ? reply : errmess([0],reply);
	}
	for(var i=0;i<PROOF.length;i++) {
		try {
			ckRest(PROOF[i],1);
		} catch(err) {
			reply = 'ERROR: There is a problem with proof line '+(i+1)+'.  The error message concerning it is:<br /><br />'+err;
			return f==1 ? reply : errmess([0,(i+1)],reply);
		}
	}
	var lastln = PROOF[PROOF.length-1];
	for(var i=0;i<lastln.sig.length;i++) {
		if(lastln.sig[i]!=1) {
			reply = 'WARNING: proof is incomplete.  The final line of your proof depends on line '+lastln.sig[i]+', which is not a Premise!';
			return f==1 ? reply : errmess([0],reply);
		}
	}
	if(lastln.frm!=CONCLUSION[0]) {
		reply = 'WARNING: proof is incomplete.  The final line of your proof does not match the conclusion '+CONCLUSION[0]+' you are aiming for.';
		return f==1 ? reply : errmess([0],reply);
	}
	reply = 'Proof checks out!';
	return f==1 ? reply : errmess([2],reply);
}


// Exports a proof
function export_proof() {
	if(PROOF.length==0) {return errmess([0],'No proof to export.');}
	var plain = document.getElementById('plain').checked;
	var pretty = document.getElementById('pretty').checked;
	var latex = document.getElementById('latex').checked;

	var ocnt = PROOF.map(function(a) {return a.cnt.toString();});
	var ofrm = pretty ? PROOF.map(function(a) {return padBCs(richardify(a.frm));}) : PROOF.map(function(a) {return padBCs(a.frm);});
	ofrm = latex ? PROOF.map(function(a) {return latexify(richardify(a.frm));}) : ofrm;
	var ocnl = pretty ? padBCs(richardify(CONCLUSION[0])) : padBCs(CONCLUSION[0]);
	ocnl = latex ? latexify(richardify(CONCLUSION[0])) : ocnl;
	var pre = '';
	var olin = PROOF.map(function(a) {return linD(a.lin);});
	var orul = (pretty || latex) ? PROOF.map(function(a) {return gRul(a.rul);}) : PROOF.map(function(a) {return a.rul;});
	var odth = latex ? mkodth('\\fa ','\\fh ') : mkodth('| ','|_');
	var proof = '';

	if(plain || pretty) {
		var pre = pre+'Problem: '
		var a = PROOF.filter(function(a) {return a.rul=="Premise";});
		for(var i=0;i<a.length;i++) {
			pre = i==a.length-1 ? pre+ofrm[i] : pre+ofrm[i]+', ';
		}
		pre = pre+' |- '+ocnl+'\r\n\r\n';
		ofrm = mkofrm(odth,ofrm,'  ');
		var mc = max(ocnt)+2;
		var mf = max(ofrm)+4;
		for(var i=0;i<PROOF.length;i++) {
			if(olin[i].length==0) {
				proof += ocnt[i]+w(mc-ocnt[i].length)+ofrm[i]+w(mf-ofrm[i].length)+orul[i]+'\r\n';
			} else {
				proof += ocnt[i]+w(mc-ocnt[i].length)+ofrm[i]+w(mf-ofrm[i].length)+olin[i]+'  '+orul[i]+'\r\n';
			}
		}
	}
	if(latex) {
		pre = pre+'\%NOTE: requires \\usepackage{fitch}\r\n\\noindent Problem: $';
		var a = PROOF.filter(function(a) {return a.rul=="Premise";});
		for(var i=0;i<a.length;i++) {
			pre = i==a.length-1 ? pre+ofrm[i] : pre+ofrm[i]+', ';
		}
		pre = pre+' \\vdash '+ocnl+'$\\\\\r\n\\vspace{1em}\r\n\r\n';
		proof = '\\begin{fitch}\r\n';
		ofrm = mkofrm(odth,ofrm,'');
		orul = orul.map(lxrul);
		for(var i=0;i<PROOF.length;i++) {
			if(olin[i].length==0) {
				proof += ofrm[i]+' & '+orul[i]+'\\\\\r\n';
			} else {
				proof += ofrm[i]+' & '+olin[i]+'  '+orul[i]+'\\\\\r\n';
			}
		}
		proof = proof+'\\end{fitch}';
	}

	document.getElementById('importarea').value = pre+proof;

	function mkodth(db,fb) { // makes depth lines and inserts fitch bar, with db the depth line symbol and fb the horizontal fitch bar symbol
		var out = [];
		for(var i = 0;i<PROOF.length;i++) {
			var s = '';
			for(var j=0;j<PROOF[i].dth;j++) {
				if(j!=PROOF[i].dth-1) {
					s = s+db;
				} else if(i==orul.lastIndexOf('Premise')) { // uses '\fj' rather than '\fh' for horizontal bar on last premise line in latex
					s = latex ? s+'\\fj ' : s+fb;
				} else {
					s = (orul[i]=='Assumption'||orul[i]=='Flag') ? s+fb : s+db;
				}
			}
			out.push(s);
		}
		return out;
	}
	// Int -> String
	// Produces a string of n white spaces
	function w(n) {
		var s = '';
		for(var i=0;i<n;i++) {s = s+' ';}
		return s;
	}
	function mkofrm(a1,a2,sp) {
		for(var i=0;i<a1.length;i++) {a2[i] = a1[i]+sp+a2[i];}
		return a2;
	}
	function lxrul(s) {
		var out = '';
		var test = '';
		for(var i=0;i<s.length;i++) {
			test = utox(s[i]);
			if(test!=s[i]) {test='$'+test+'$';}
			out += test;
		}
		return out;
	}
}


// imports a proof from the importarea
function import_proof() {
	try {var extract = extract_proof();} catch(err) {return errmess([0],err);}
	var prePROOF = extract[0];
	var problem = extract[1];
	clearall();
	CONCLUSION.push(problem[1]);

	for(var i=0;i<prePROOF.length;i++) {
		if(prePROOF[i].rul=='Premise' && problem[0].indexOf(prePROOF[i].frm)<0) {
			return errmess([0],"ERROR: Your proof contains the following formula as a premise on line "+(i+1)+": "+prePROOF[i].frm+". This is not among the premises in the problem you entered.  Problem is:<br/>"+problem[0].join(',')+ " |- "+problem[1]);
		}
		try {validate_line(prePROOF[i]);} catch(err) {
			PROOF = [];
			PROOF = prePROOF.slice(0,i);
			draw_conclusion();
			draw();
			return errmess([0],"ERROR: There is a problem with line "+(i+1)+" in the proof you are attempting to import.  The error message concerning it is:<br><br>"+err+"<br><br>The portion of the proof that was successfully validated is to the left.");
		}
		PROOF.push(prePROOF[i]);
	}
	if(prePROOF[prePROOF.length-1].frm!=problem[1]) {
		errmess([0], "Proof successfully imported.  WARNING: the last line of the proof does not match the conclusion in the problem line.");
	} else {
		errmess([2],"Proof successfully imported. Proof is complete!");
	}
	document.getElementById('importarea').value = 'Paste a previously exported proof (in plain notation) here and import it by clicking the button. NOTE: you can edit a proof here, but you need to be careful about formatting.  E.g. make sure the proof begins with a "Problem: " line, that formulas contain outermost parentheses, and that there are at least two spaces separating each "column" of the proof, with no double spaces elsewhere.';
	draw_conclusion();
	draw();
}

// extracts proof from the text in the importarea returns a two element array: first
// element is the extracted proof, second is the extracted problem (from the problem line)
function extract_proof() {
	var proof = document.getElementById('importarea').value;

	if(proof.indexOf("Paste a previously")==0) {throw "ERROR: paste a proof into the textarea first.";}

	var prePROOF = [];
	var tmp = next_line(proof); // A two-element array, first the line, second the rest of the proof
	var line = [];
	var c = 0;
	var f = '';
	var t = [];
	var r = '';
	var s = [];
	var l = '';
	var d = 0;

	while(tmp[0].indexOf('Problem: ')!=0 && proof.length!=0) { // consumes until problem line
		proof = tmp[1];
		tmp = next_line(proof);
	} // report error if no problem line found
	if(proof.length==0) {throw 'ERROR: proofs must begin with a problem line.  Something like "Problem: (P>Q), P |- Q"';}
	try{var problem = get_problem(tmp[0]);} catch(err) {return errmess([0],err);} // extracts problem from problem line

	while(proof.length!=0 && (tmp[0].length==0 || (tmp[0][0]!=' ' && !isInt(tmp[0][0])))) { // consumes until proof starts
		proof = tmp[1];
		tmp = next_line(proof);
	}
	if(proof.length==0) {return nope();} // error if no proof found

	tmp = next_line(proof);

	while(tmp[0].length!=0) { // collects proof lines till we run out
		line = tmp[0].split('  ').filter(fltr); // removes blank array elements
		line = line.map(function(x) {return x.replace(/ /g,'');}); // removes whitespace
		proof = tmp[1];
		tmp = next_line(proof);
		if(line.length==5) { // line has all five rule columns: 0cnt 1dth 2frm 3lin 4rul
			c = parseInt(line[0],10); // line count
			f = line[2];
			t = parse(f);
			r = line[4];
			s = doSI(r);
			l = line[3];
			d = line[1].match(/\|/g).length; // line depth
		} else { // line either has depth of 0 or no rule lines
			var f = 0;
			for(var i=0;i<line.length;i++) {
				var test = parse(line[i]);
				if(test.length>0 && test.length<4) { // require less than 4 because rules like 'Premise' can pass parsing
					f = i;
					break;
				}
			}
			if(f==1) { // line has depth of 0: 0cnt 1frm 2lin 3rul
				c = parseInt(line[0],10);
				d = 0;
				f = line[1];
				t = parse(f);
				r = line[3];
				s = doSI(r);
				l = line[2];
			} else if(f==2) { // line has no rule lines: 0cnt 1dth 2frm 3rul
				c = parseInt(line[0],10);
				d = line[1].match(/\|/g).length; // line depth
				f = line[2];
				t = parse(f);
				r = line[3];
				s = doSI(r);
				l = '';
			} else if(line[3]=='Flag') { // line is a flagging step: 0cnt 1dth 2frm 3rul, Note flagging steps can't have depth 0
				c = parseInt(line[0],10);
				d = line[1].match(/\|/g).length; // line depth
				f = line[2];
				t = [];
				r = line[3];
				s = '';
				l = '';
			} else {return nope();}
		}
		var nl = new Line(c,f,t,r,s,l,[],d);
		if(nl.rul=='Assumption') {
			if(prePROOF.length>0) {
				if(prePROOF[prePROOF.length-1].dth==nl.dth) {
					nl.sig=['-'];
				} else {
					nl.sig=['+'];
				}
			} else {
				nl.sig = ['+'];
			}
		}
		prePROOF.push(nl);
	}

	return [prePROOF,problem];

	// BELOW are some helper functions used by extract_proof()

	function next_line(str) {
		var x = str.indexOf('\n');
		if(x!=(-1)) {
			return [str.substring(0,x),str.substring(x+1)];
		} else {
			return[str,'']
		}
	}

	function testr(str) {
		var t = ['\u2228','\u2200','\u2203','\u2192','\u2194','\u22A5'];
		for(var i=0;i<t.length;i++) {
			if(str.indexOf(t[i])>=0) {return true;}
		}
		return false;
	}
	function fltr(x) {
		if(x.length==0) {return false;}
		hascontent = false;
		for(var i=0;i<x.length;i++) {
			if(x[i]!=' ') {hascontent = true;}
		}
		return hascontent;
	}

	function doSI(r) {
		if(r.indexOf('(')<0) {return [];}
		var SIs = document.getElementById('siti').childNodes;
		for(var i=1;i<SIs.length;i++) {
			if(i%2==0) {continue;} // NOTE: need this because 0 and even elements of the childNodes of a <select> are #text, which have no value
			if(SIs[i].value.indexOf(r)==0) {
				return getSeq(SIs[i].value);
			}
		}
	}

	function nope() {
		throw "ERROR: Something is wrong with the formatting of the proof you entered.";
	}
}

// takes a string (from import_proof) and extracts the premises and conclusion
// returns a two element array: first element an array of premises, second the
// conclusion string
function get_problem(str) {
	str = str.replace('Problem: ',''); // remove the 'Problem: ' part
	str = str.replace('|-',','); // remove the vdash
	str = str.replace('\u22A2',','); // remove the vdash
	str = str.replace(/ /g,''); // remove whitespace
	str = str.split(','); // split on commas
	str = str.filter(function(x) {return x.length!=0;}); // remove empty elements (you get these if problem is a theorem)
	var tmp = '';
	for(var i=0;i<str.length;i++) { // check if any of the formulas are ill formed
		if(parse(str[i]).length==0) {
			throw "ERROR: the following formula in the Problem line is ill-formed: "+str[i]+". Make sure outermost parentheses are included.";
		}
	}
	return [str.slice(0,str.length-1),str[str.length-1]];
}

// clears the proof
function clearall() {
	PROOF = [];
	GOALS = [];
	CONCLUSION = [];
	draw_conclusion();
	draw();
	draw_goals();
}

// start a new proof
function restart_proof() {
	clearall();
	clear_app();
	errmess([1],'');
	disp('app');
}

// check if proof is complete
function checkifdone() {
	var prems = PROOF.filter(function(a) {return a.rul=="Premise";}).length;
	var lastln = PROOF[PROOF.length-1];
	if(lastln.frm==CONCLUSION[0] && ((prems==0 && lastln.sig.length==0) || (prems>0 && same(lastln.sig,[1])))) {
		errmess([2],"Your proof is complete!  Ready to export.");
		GOALS = [];
		draw_goals();
	} else {errmess([1],'');}
}

// Displays error message.  The second parameter is the message, and the first
// is an array, of either one or two elements.  The first element is 0 for displaying
// on a red background (errors), 1 for displaying on blue, and 2 for displaying on green.
// The second (optional) element gives the line number on which the error occurred.
// NOTE: error line number currently being ignored (I used  to  highlight the line with
// the error in red).
function errmess(n,mess) {
	var erel = document.getElementById('errord');
	if(n[0]==0) { // display on red
		erel.style.border = 'solid 1px #FF0000';
		erel.style.backgroundColor = '#FF9999';
		erel.innerHTML = mess;
	} else if(n[0]==1) { // display on blue
		erel.style.border = 'solid 1px #B4BAEA';
		erel.style.backgroundColor = '#F0F4FF';
		erel.innerHTML = mess;
	} else if(n[0]==2) { // display on green
		erel.style.border = 'solid 1px #87D51C';
		erel.style.backgroundColor = '#E3FFB8';
		erel.innerHTML = mess;
	}
	document.getElementById('rul').value = '--Select--';
	document.getElementById('lin').value = '';
	document.getElementById('dth').value = 'Plus 1';
	show('rul');
}
