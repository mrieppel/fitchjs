// RULE CHECKING FUNCTIONS, PROPOSITIONAL LOGIC
// =============================================

// Note: the value n that is the second parameter in the functions below sets whether
// certain rule-specific line properties need to be set (with value n of 0), or not (with 
// value n of 1).  (The userio function ckproof() checks rule applications, but assumes
// rule-specific parameters were all filled during append.)

// Premises
function ckPR(l,n) {
	var flag = '[ERROR applying Premise rule]: ';
	if(n==0) {
		l.sig = [1];
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = freeVars(l.tr);
	}
	if(l.lin.length>0) {
		throw flag+'Premise rule can\'t be applied to any lines.';
	}
	for(var i=0;i<l.cnt-1;i++) {
		if(PROOF[i].rul!='Premise') {
			throw flag+'Premises must be entered as the first lines of the proof.';
		}
	}
}

// Assumptions
function ckAS(l,n) {
	var flag = '[ERROR with Assumption]: ';
	var flag = l.sig;
	
	if(n==0) {
		if(!PROOF.length) {
			l.sig = [l.cnt];
		} else {
			if(flag[0]=='+') {
				l.sig = PROOF[l.cnt-2].sig.concat([l.cnt]);
			} else {
				l.sig = PROOF[l.cnt-2].sig.slice(0,PROOF[l.cnt-2].sig.length-1).concat([l.cnt]);
			}
		}
		l.dth = l.sig.length;
		l.avl = gtAvl(l);
		l.frv = freeVars(l.tr);
	}
	
	if(l.lin.length>0) {
		throw flag+'Assumptions should not cite any rule lines.';
	}
}


// Reit: Reiteration of line
function ckRE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'Rule must be applied to one line.';
	}
	if(l.frm!=PROOF[l.lin[0]-1].frm) {
		throw flag+'The formula being derived must be the same as the formula on the rule line.';
	}
	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// &I: Conjunction Introduction
function ckCJI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'Rule must be applied to two lines.';
	}
	if(l.tr.length!=3 || l.tr[1]!='&') {
		throw flag+'The formula being derived must be a conjunction.';
	}
	if(!(l.frm=='('+PROOF[l.lin[0]-1].frm+'&'+PROOF[l.lin[1]-1].frm+')') && !(l.frm=='('+PROOF[l.lin[1]-1].frm+'&'+PROOF[l.lin[0]-1].frm+')')) {
		throw flag+'The formulas on lines '+l.lin[0]+' and '+l.lin[1]+' must be the conjuncts of the formula being derived.';
	}
	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// &E: Conjunction Elimination
function ckCJE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'Rule must be applied to one line.';
	}
	if(PROOF[l.lin[0]-1].tr.length!=3 || PROOF[l.lin[0]-1].tr[1]!='&') {
		throw flag+'The formula on line '+l.lin[0]+' must be a conjunction.';
	}
	if(!(l.frm==unparse(PROOF[l.lin[0]-1].tr[0])) && !(l.frm==unparse(PROOF[l.lin[0]-1].tr[2]))){
		throw flag+'The formula being derived must be one of the conjuncts of the formula on line '+l.lin[0]+'.';
	}
	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}


// >I: Conditional Introduction
function ckCNI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(l.lin.length!=3 || l.lin[1]!="-") {
		throw flag+'Rule must be applied to one subproof (citation of the form "j-k").';
	}
	
	var sa = l.lin[0], // line number of subproof assumption
		sc = l.lin[2]; // line number of subproof conclusion
	
	if(PROOF[sa-1].rul!="Assumption") {
		throw flag+"The first rule line must be an assumption.";
	}
	if(!same(PROOF[sa-1].sig,PROOF[sc-1].sig)) {
		throw flag+'The two rule lines must be in the same subproof.';
	}
	
	var ll = lastline(PROOF[sa-1].sig);
	if(ll!=sc) {
		throw flag+'The second rule line must be the last line of the subproof beginning with the assumption line '+sa+".";
	}
	
	if(l.tr.length!=3 || l.tr[1]!='>') {
		throw flag+'The formula being derived must be a conditional.';
	}
	if(PROOF[sa-1].frm!=unparse(l.tr[0])) {
		throw flag+'The assumption on the first rule line must be the antecedent of the conditional being derived.';
	}
	if(PROOF[sc-1].frm!=unparse(l.tr[2])) {
		throw flag+'The second rule line must be the consequent of the conditional being derived.';
	}
		
	if(n==0) {fillD(l,sc);} // set dth, sig, avl, and frv properties
	
	if(!same(l.sig,PROOF[sc-1].sig.slice(0,PROOF[sc-1].sig.length-1))) {
		throw flag + "The subproof "+linD(l.lin)+" you are citing is not available at this stage in the proof.";
	}
}

// >E: Conditional Elimination
function ckCNE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'Rule must be applied to two lines.';
	}
	if(PROOF[l.lin[0]-1].tr.length!=3 || PROOF[l.lin[0]-1].tr[1]!='>') {
		throw flag+'The first rule line must be a conditional.'
	}
	if(PROOF[l.lin[1]-1].frm!=unparse(PROOF[l.lin[0]-1].tr[0])) {
		throw flag+'The second rule line must be the antecedent of the conditional on the first rule line.';
	}
	if(l.frm!=unparse(PROOF[l.lin[0]-1].tr[2])) {
		throw flag+'The formula being derived must be the consequent of the conditional on the first rule line.';
	}

	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// vI: Disjunction Introduction
function ckDJI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to line '+l.lin.join(',')+']: '
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'Rule must be applied to one line';
	}
	if(l.tr.length!=3 || l.tr[1]!='v') {
		throw flag+'The formula being derived must be a disjunction.';
	}
	if(!(unparse(l.tr[0])==PROOF[l.lin[0]-1].frm) && !(unparse(l.tr[2])==PROOF[l.lin[0]-1].frm)) {
		throw flag+'The formula on line '+l[0]+' must be a disjunct of the formula being derived.';
	}

	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+a.join(',');
	}
}

// vE: Disjunction Elimination
function ckDJE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(l.lin.length!=7 || l.lin[2]!="-" || l.lin[5]!="-") {
		throw flag+'Rule must be applied to a disjunction line and a pair of subproofs (with subproof citations of the form "j-k").';
	}
	
	var dl = l.lin[0], // disjunction line
		sa1 = l.lin[1], // first subproof assumption
		sc1 = l.lin[3], // first subproof conclusion
		sa2 = l.lin[4], // second subproof assumption
		sc2 = l.lin[6]; // second subproof conclusion

	if(PROOF[dl-1].tr[1]!='v') {
		throw flag+'The first rule line must be a disjunction.';
	}
	if(PROOF[sa1-1].rul!='Assumption' || PROOF[sa2-1].rul!='Assumption') {
		throw flag+'The second and fourth rule lines must be assumptions.';
	}
	
	if(!same(PROOF[sa1-1].sig,PROOF[sc1-1].sig)) {
		throw flag+'The second and third rule lines must be in the same subproof.';
	}
	if(!same(PROOF[sa2-1].sig,PROOF[sc2-1].sig)) {
		throw flag+'The fourth and fifth rule lines must be in the same subproof.';
	}
	
	var ll = lastline(PROOF[sa1-1].sig);
	if(ll!=sc1) {
		throw flag+'The third rule line must be the last line of the subproof beginning with the assumption '+sa1+".";
	}
	ll = lastline(PROOF[sa2-1].sig);
	if(ll!=sc2) {
		throw flag+'The fifth rule line must be the last line of the subproof beginning with the assumption '+sa2+".";
	}
	
	if(PROOF[sa1-1].frm!=unparse(PROOF[dl-1].tr[0])) {
		throw flag+'The second rule line should be the left disjunct of '+PROOF[dl-1].frm+'.';
	}
	if(PROOF[sa2-1].frm!=unparse(PROOF[dl-1].tr[2])) {
		throw flag+'The fourth rule line should be the right disjunct of '+PROOF[dl-1].frm+'.';
	}
	if(PROOF[sc1-1].frm!=l.frm || PROOF[sc2-1].frm!=l.frm) {
		throw flag+'The third and fifth rule lines must match the formula being derived.';
	}
	
	if(n==0) {fillD(l,sc2);} // set dth, sig, avl, and frv properties
	
	if(!same(l.sig,PROOF[sc1-1].sig.slice(0,PROOF[sc1-1].sig.length-1))) {
		throw flag + "The first subproof you are citing is not available at this stage in the proof.";
	}
	if(!same(l.sig,PROOF[sc2-1].sig.slice(0,PROOF[sc2-1].sig.length-1))) {
		throw flag + "The second subproof you are citing is not available at this stage in the proof.";
	}
	
	var x = areAvl([dl],l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// ~I: Negation Introduction
function ckNI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(l.lin.length!=3 || l.lin[1]!="-") {
		throw flag+'Rule must be applied to one subproof (citation of the form "j-k").';
	}
	
	var sa = l.lin[0], // line number of subproof assumption
		sc = l.lin[2]; // line number of subproof conclusion
	
	if(PROOF[sa-1].rul!="Assumption") {
		throw flag+"The first rule line must be an assumption.";
	}
	if(!same(PROOF[sa-1].sig,PROOF[sc-1].sig)) {
		throw flag+'The two rule lines must be in the same subproof.';
	}
	
	var ll = lastline(PROOF[sa-1].sig);
	if(ll!=sc) {
		throw flag+'The second rule line must be the last line of the subproof beginning with assumption '+sa+".";
	}

	if(PROOF[sc-1].frm!='#') {
		throw flag+'The second rule line must be the absurdity.';
	}	 
	if(l.frm!=('~'+PROOF[sa-1].frm)) {
		throw flag+'The formula being derived must be the negation of the assumption on the first rule line.';
	}
	
	if(n==0) {fillD(l,sc);} // set dth, sig, avl, and frv properties
	
	if(!same(l.sig,PROOF[sc-1].sig.slice(0,PROOF[sc-1].sig.length-1))) {
		throw flag + "The subproof "+linD(l.lin)+" you are citing is not available at this stage in the proof.";
	}
}


// ~E: Negation Elimination
function ckNE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'Rule must be applied to two lines.';
	}
	if(l.frm!='#') {
		throw flag+'The formula being derived must be the absurdity, #.';
	}
	if(PROOF[l.lin[0]-1].frm!='~'+PROOF[l.lin[1]-1].frm && '~'+PROOF[l.lin[0]-1].frm!=PROOF[l.lin[1]-1].frm) {
		throw flag+'One of lines '+l.lin[0]+' or '+l.lin[1]+' must be the negation of the other.';
	}
	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// DN: Double Negation Elimination
function ckDN(l,n) {
	var flag = '[ERROR applying DN to line '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'Rule must be applied to one line.';
	}
	if(!(PROOF[l.lin[0]-1].frm.length>2) || PROOF[l.lin[0]-1].frm.substr(0,2)!='~~' || l.frm!=PROOF[l.lin[0]-1].frm.substring(2)) {
		throw flag+'Formula on line '+l.lin[0]+' must be the double negation of the formula being derived.';
	}
	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}

// EFQ: Ex Falso Quodlibet
function ckEFQ(l,n) {
	var flag = '[ERROR applying EFQ to line '+l.lin.join(',')+']: ';
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=1) {
		throw flag+'Rule must be applied to one line.';
	}
	if(PROOF[l.lin[0]-1].frm!='#') {
		throw flag+'Formula on line '+l.lin[0]+' must be the absurdity.';
	}
	x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}

}

// <>I: Biconditional Introduction
function ckBCI(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+linD(l.lin)+']: ';
	
	if(l.lin.length!=6 || l.lin[1]!="-" || l.lin[4]!="-") {
		throw flag+'Rule must be applied to two subproofs (citations of the form "j-k").';
	}
	
	if(l.tr.length!=3 || l.tr[1]!='<>') {
		throw flag+'The formula being derived must be a biconditional.';
	}
	
	var sa1 = l.lin[0], // assumption of first subproof
		sc1 = l.lin[2], // conclusion of second subproof
		sa2 = l.lin[3], // assumption of second subproof
		sc2 = l.lin[5]; // conclusion of second subproof
	
	
	if(PROOF[sa1-1].rul!='Assumption' || PROOF[sa2-1].rul!='Assumption') {
		throw flag+'The first and third rule lines must be assumptions.';
	}
	
	if(!same(PROOF[sa1-1].sig,PROOF[sc1-1].sig)) {
		throw flag+'The first and second rule lines must be in the same subproof.';
	}
	if(!same(PROOF[sa2-1].sig,PROOF[sc2-1].sig)) {
		throw flag+'The third and fourth rule lines must be in the same subproof.';
	}
	
	var ll = lastline(PROOF[sa1-1].sig);
	if(ll!=sc1) {
		throw flag+'The second rule line must be the last line of the subproof beginning with the assumption '+sa1+".";
	}
	ll = lastline(PROOF[sa2-1].sig);
	if(ll!=sc2) {
		throw flag+'The fourth rule line must be the last line of the subproof beginning with the assumption '+sa2+".";
	}

	if(PROOF[sa1-1].frm!=PROOF[sc2-1].frm || PROOF[sc1-1].frm!=PROOF[sa2-1].frm) {
		throw flag+'The formula on the first rule line must match the one on the fourth, and the one on the second must match the one on the third.';
	}
	if((l.frm!='('+PROOF[sa1-1].frm+'<>'+PROOF[sc1-1].frm+')') && (l.frm!='('+PROOF[sc1-1].frm+'<>'+PROOF[sa1-1].frm+')')) {
		throw flag+'The biconditional being derived must be composed of the formulas on the rule lines.';
	}
	
	if(n==0) {fillD(l,sc2);} // set dth, sig, avl, and frv properties
	
	if(!same(l.sig,PROOF[sc1-1].sig.slice(0,PROOF[sc1-1].sig.length-1))) {
		throw flag + "The first subproof you are citing is not available at this stage in the proof.";
	}
	if(!same(l.sig,PROOF[sc2-1].sig.slice(0,PROOF[sc2-1].sig.length-1))) {
		throw flag + "The second subproof you are citing is not available at this stage in the proof.";
	}
}

//<>E: Biconditional Elimination
function ckBCE(l,n) {
	var flag = '[ERROR applying '+gRul(l.rul)+' to lines '+l.lin.join(',')+']: '
	if(n==0) {fillND(l);}
	
	if(l.lin.length!=2) {
		throw flag+'Rule must be applied to two lines.';
	}
	if(PROOF[l.lin[0]-1].tr.length!=3 || PROOF[l.lin[0]-1].tr[1]!='<>') {
		throw flag+'The formula on the first rule line must be a biconditional.';
	}
	if('('+PROOF[l.lin[1]-1].frm+'<>'+l.frm+')'!=PROOF[l.lin[0]-1].frm && '('+l.frm+'<>'+PROOF[l.lin[1]-1].frm+')'!=PROOF[l.lin[0]-1].frm) {
		throw flag+'The formula being derived must be one side of the biconditional on the first rule line, and the formula on the second rule line the other side of it.';	
	}

	var x = areAvl(l.lin,l.avl);
	if(x>=0) {
		throw flag+'Rule line '+x+' is not available at this stage of the proof.  The following lines are available: '+l.avl.join(',');
	}
}