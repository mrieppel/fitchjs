// RULE CHECKING FUNCTIONS, QUANTIFICATIONAL LOGIC
// ===============================================

// Flag
function ckFLG(l,n) {
	var flag = '[ERROR applying Flag rule]: ';
	if(n==0) {
		if(!PROOF.length) {
			l.sig = [l.cnt];
		} else {
			l.sig = PROOF[l.cnt-2].sig.concat([l.cnt]);
		}
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = [l.frm];
	}
	
	var freevars = frvList(l.avl);
	if(freevars.indexOf(l.frm)>=0) {
		throw flag+'The flagged term '+l.frm+' already occurs in an available line.';
	}
}

// AI: Universal Introduction
function ckAI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(n==0) {
		if(!PROOF.length) {throw "[ERROR]: cannot begin a proof using "+gRul(l.rul)+".";}
		l.sig = PROOF[l.cnt-2].sig.slice(0,PROOF[l.cnt-2].sig.length-1);
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = freeVars(l.tr);
	}
	
	if(l.lin.length!=3 || l.lin[1]!="-") {
		throw flag+'There is a problem with line citation. The rule must be applied to one subproof (citation of the form "j-k").';
	}
	
	var sa = l.lin[0], // line number of subproof start (flag line)
		sc = l.lin[2]; // line number of subproof conclusion
	
	if(PROOF[sa-1].rul!="Flag") {
		throw flag+"The subproof must begin with a Flag line.";
	}
	if(!same(PROOF[sa-1].sig,PROOF[sc-1].sig)) {
		throw flag+'The two rule lines you cited are not in the same subproof.';
	}
	
	var ll = lastline(PROOF[sa-1].sig);
	if(ll!=sc) {
		throw flag+'The second rule line must be the last line of the subproof beginning with the Flag line '+sa+".";
	}
	
	if(l.tr.length!=2 || !isQ(l.tr[0]) || l.tr[0][1]!='A') {
		throw flag+'The formula being derived must be universally quantified.';
	}
	
	var iv=isInst(l.tr,PROOF[sc-1].frm);
	if(iv=='_') {
		throw flag+'The formula that concludes the cited subproof is not an instance of the universal being derived.';
	}
	if(iv!='+' && iv!=PROOF[sa-1].frm) { // the first test is to allow vacuous quantification
		throw flag+'The constant being generalized on must be the one flagged at the beginning of the subproof.';
	}
	if(l.frv.indexOf(iv)>=0) {
		throw flag+'Every occurrence of the term \''+iv+'\' in line '+sc+' has to be replaced with the variable bound by the quantifier being introduced.';
	}
	if(n==0) {fillD(l,sc);} // set dth, sig, avl, and frv properties
	
	if(!same(l.sig,PROOF[sc-1].sig.slice(0,PROOF[sc-1].sig.length-1))) {
		throw flag + "The subproof "+linD(l.lin)+" you are citing is not available at this stage in the proof.";
	}

}

// AE: Universal Elimination
function ckAE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'There is a problem with line citation. The rule must be applied to one line.';
	}
	if(PROOF[l.lin[0]-1].tr.length!=2 || !isQ(PROOF[l.lin[0]-1].tr[0]) || PROOF[l.lin[0]-1].tr[0][1]!='A') {
		throw flag+'The formula the rule is being applied to is not universally quantified.';
	}
	var iv = isInst(PROOF[l.lin[0]-1].tr,l.frm);
	if(iv=='_') {
		throw flag+'The formula being derived is not an instance of the universally quantified formula on line '+l.lin[0]+'.';
	}
	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}


// EI: Existential Introduction
function ckEI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'There is a problem with line citation. The rule should be applied to one line.';
	}
	if(l.tr.length!=2 || !isQ(l.tr[0]) || l.tr[0][1]!='E') {
		throw flag+'The formula being derived is not existentially quantified.'; 
	}
	var iv = isInst(l.tr,PROOF[l.lin[0]-1].frm);
	if(iv=='_') {
		throw flag+'The formula on line '+l.lin[0]+' is not an instance of the formula being derived.';
	}

	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// EE: Existential Elimination
function ckEE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(l.lin.length!=4 || l.lin[2]!="-") {
		throw flag+'There is a problem with line citation.  The rule must be applied to a line containing a existential statement and a subproof (citation of the form "j-k").';
	}
	
	var ex = l.lin[0], // line of the existential
		sa = l.lin[1], // line of subproof assumption
		sc = l.lin[3]; // line of subproof conclusion
	
	if(PROOF[ex-1].tr.length!=2 || !isQ(PROOF[ex-1].tr[0]) || PROOF[ex-1].tr[0][1]!='E') {
		throw flag+'The formula on the first rule line must be an existentially quantified formula.';
	}
	
	var iv = isInst(PROOF[ex-1].tr,PROOF[sa-1].frm);
	
	if(!same(PROOF[sa-1].sig,PROOF[sc-1].sig)) {
		throw flag+'The lines'+sa+'-'+sc+' you cited are not part of the same subproof.';
	}
	
	if(PROOF[sa-1].rul!='Assumption' || iv=='_') {
		throw flag+'The first line of the subproof you cited is either not an assumption, or not an instance of the existential formula on the first rule line.';
	}
		
	var ll = lastline(PROOF[sa-1].sig);
	if(ll!=sc) {
		throw flag+'Line '+sc+' is not the last line of the subproof beginning with the assumption line '+sa+".";
	}
		
	if(PROOF[sc-1].frm!=l.frm) {
		throw flag+'The formula being derived must match the last formula in the subproof you cited.';
	}
		
	if(n==0) {fillD(l,sc);} // set dth, sig, avl, and frv properties
		
	if(l.frv.indexOf(iv)>=0) {
		throw flag+'The individual constant \''+iv+'\' introduced in the assumption on line '+sa+' cannot occur in the formula being derived.';
	}
	
	var freevars = frvList(PROOF[sa-1].avl);
	if(freevars.indexOf(iv)>=0) {
		throw flag+'Flagging violation.  The individual constant \''+iv+'\' introduced in the assumption already occurs in a line available to that assumption.'
	}	
	
	if(!same(l.sig,PROOF[sc-1].sig.slice(0,PROOF[sc-1].sig.length-1))) {
		throw flag + "The subproof you are citing is not available at this stage in the proof.";
	}
}


// IDI: Identity Introduction
function ckIDI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+']: ';
	
	if(l.lin.length!=0) {
		throw flag+'There is a problem with line citation. This rule should not be applied to any lines.'
	}
	if(l.tr.length!=3 || l.tr[1]!='=' || l.tr[0]!=l.tr[2]) {
		throw flag+'The formula entered is not of the form \'t=t\'.';
	}
	if(l.cnt==1) {l.sig = [];} else {l.sig = PROOF[l.cnt-2].sig.slice(0);}
	l.dth = l.sig.length;
	l.avl = gtAvl(l);
	l.frv = freeVars(l.tr);
}

// IDE: Identity Elimination
function ckIDE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'There is a problem with line citation. The rule must be applied to two lines.';
	}
	if(PROOF[l.lin[0]-1].tr.length!=3 || PROOF[l.lin[0]-1].tr[1]!='=') {
		throw flag+'The first rule line needs to be an identity.'
	}
	if(!checkID(PROOF[l.lin[0]-1].tr,PROOF[l.lin[1]-1].tr,l.frm)) {
		throw flag+'The formula being derived does not follow by =E.'
	}

	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// SI(QS): Quantifier Shift
function ckQS(l,n) {
	var flag = '[ERROR applying SI(QS) to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'There is a problem with line citation. The rule must be applied to one line.';
	}
	var rl = l.lin[0]-1;
	if(l.tr.length!=2 || l.tr[1].length!=2 || PROOF[rl].tr.length!=2 || PROOF[rl].tr[1].length!=2) {
		nope();
	}
	if(isU(PROOF[rl].tr[0]) && isQ(PROOF[rl].tr[1][0])) {
		var rest = unparse(PROOF[rl].tr[1][1]);
		var oq = PROOF[rl].tr[1][0];
		var nq = flip(oq);
		var frm = nq+'~'+rest;
		if(l.frm!=frm) {nope();}
		
	} else if(isQ(PROOF[rl].tr[0]) && isU(PROOF[rl].tr[1][0])) {
		var rest = unparse(PROOF[rl].tr[1][1]);
		var oq = PROOF[rl].tr[0];
		var nq = flip(oq);
		var frm = '~'+nq+rest;
		if(l.frm!=frm) {nope();}
	} else {nope();}

	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
	function nope() {
		throw flag+'The formula being derived does not follow by SI(QS).'
	}
	function flip(q) {
		var dic = {A: 'E',E: 'A'};
		return '('+dic[q[1]]+q[2]+')';
	}
}

// SI(AV): Alphabetic Variants
function ckAV(l,n) {
	var flag = '[ERROR applying SI(AV) to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'There is a problem with line citation. The rule must be applied to one line.';
	}
	if(!isAV(PROOF[l.lin[0]-1].tr,PROOF[l.lin[0]-1].frm,l.frm)) {
		throw flag+'The formula being derived is not a single variable alphabetic variant of the formula on line '+l.lin[0]+'.' 
	}

	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}