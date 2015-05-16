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
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin[0]+']: ';
	
	if(n==0) {
		if(!PROOF.length) {throw "[ERROR]: cannot begin a proof using "+gRul(l.rul)+".";}
		l.sig = PROOF[l.cnt-2].sig.slice(0,PROOF[l.cnt-2].sig.length-1);
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = freeVars(l.tr);
	}
	
	if(l.lin.length!=2) {
		throw flag+'The rule must be applied to two lines.';
	}
	if(!same(PROOF[l.cnt-2].sig,PROOF[l.lin[1]-1].sig)) {
		throw flag+'The current line should immediately follow the subproof containing the two rule lines';
	}	
	if(PROOF[l.lin[0]-1].rul!='Flag') {
		throw flag+'The first rule line must be a flagging step.';
	}
	if(l.tr.length!=2 || !isQ(l.tr[0]) || l.tr[0][1]!='A') {
		throw flag+'The formula being derived is not universally quantified.';
	}
	
	var iv=isInst(l.tr,PROOF[l.lin[1]-1].frm);
	if(iv=='_') {
		throw flag+'The formula on the second rule line is not an instance of the universal being derived.';
	}
	if(iv!=PROOF[l.lin[0]-1].frm) {
		throw flag+'The constant being generalized on must be the one flagged on the first rule line.';
	}
	if(l.frv.indexOf(iv)>=0) {
		throw flag+'Every occurrence of the term \''+iv+'\' in line '+l.lin[1]+' has to be replaced with the variable bound by the quantifier being introduced.';
	}
	if(!same(PROOF[l.lin[1]-1].sig,PROOF[l.lin[0]-1].sig)) {
		throw flag+'The two rule lines should be in the same subproof.';
	}
}

// AE: Universal Elimination
function ckAE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'The rule must be applied to one line.';
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
		throw flag+'The rule is being applied to an inappropriate number of lines.';
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
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	
	if(n==0) {
		if(!PROOF.length) {throw "[ERROR]: cannot begin a proof using "+gRul(l.rul)+".";}
		l.sig = PROOF[l.cnt-2].sig.slice(0,PROOF[l.cnt-2].sig.length-1);
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = freeVars(l.tr);
	}
	
	if(l.lin.length!=3) {
		throw flag+'The rule must be applied to three lines.';
	}
	var ex = l.lin[0]-1;
	if(PROOF[ex].tr.length!=2 || !isQ(PROOF[ex].tr[0]) || PROOF[ex].tr[0][1]!='E') {
		throw flag+'The first rule line must be an existentially quantified formula.';
	}
	var ass = l.lin[1]-1;
	var iv = isInst(PROOF[ex].tr,PROOF[ass].frm);
	if(PROOF[ass].rul!='Assumption' || iv=='_') {
		throw flag+'The second rule line is either not an assumption, or not an instance of the existential formula on the first rule line.';
	}
	var cl = l.lin[2]-1;
	if(PROOF[cl].frm!=l.frm) {
		throw flag+'The formula being derived must match the formula on the third rule line.';
	}
	if(!same(PROOF[l.lin[1]-1].sig,PROOF[l.lin[2]-1].sig)) {
		throw flag+'The formulas on the second and third rule lines must occur in the same subproof.'
	}
	if(!same(PROOF[l.cnt-2].sig,PROOF[l.lin[1]-1].sig)) {
		throw flag+'The line you are entering should immediately follow the subproof containing the two rule lines.';
	}
	if(l.frv.indexOf(iv)>=0) {
		throw flag+'The term \''+iv+'\' introduced in the assumption cannot occur in the formula being derived.';
	}
	var freevars = frvList(PROOF[l.lin[1]-1].avl);
	if(freevars.indexOf(iv)>=0) {
		throw flag+'Flagging violation.  The term \''+iv+'\' introduced in the assumption already occurs in a line available to that assumption.'
	}
}

// IDI: Identity Introduction
function ckIDI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+']: ';
	
	if(l.lin.length!=0) {
		throw flag+'This rule should not be applied to any lines.'
	}
	if(l.tr.length!=3 || l.tr[1]!='=' || l.tr[0]!=l.tr[2]) {
		throw flag+'The formula entered is not of the form \'t=t\'.';
	}
	
	if(!PROOF.length) {l.sig = [l.cnt];} else { l.sig = PROOF[l.cnt-2].sig.slice(0);}
	l.dth = l.sig.length;
	l.avl = gtAvl(l);
	l.frv = freeVars(l.tr);
}

// IDE: Identity Elimination
function ckIDE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'The rule must be applied to two lines.';
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
		throw flag+'The rule must be applied to one line.';
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

	var x = areAvl(l,a);
	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
	function nope() {
		throw flag+'The formula being derived does not follow by SI(QS).'
	}
	function flip(q) {
		var dic = {A: 'E',E: 'A'};
		return dic[q[0]]+q[1];
	}
}

// SI(AV): Alphabetic Variants
function ckAV(l,n) {
	var flag = '[ERROR applying SI(AV) to line '+l.lin[0]+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'The rule must be applied to one line.';
	}
	if(!isAV(PROOF[l.lin[0]-1].tr,PROOF[l.lin[0]-1].frm,l.frm)) {
		throw flag+'The formula being derived is not a single variable alphabetic variant of the formula on line '+l.lin[0]+'.' 
	}

	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}
