function disp(id) {
	var menu_items = ['appm','expm','refm'];
	var menu_contents = ['prbt','appt','expt','reft'];
	var proof_started = PROOF.length>0 || CONCLUSION.length>0;
	for(var i=0;i<menu_items.length;i++) {
		document.getElementById(menu_items[i]).style.backgroundColor = '#DDDDDD';
	}
	for(var i=0;i<menu_contents.length;i++) {
		document.getElementById(menu_contents[i]).style.display='none';
	}
	var show_table = (id=='app' && !proof_started) ? 'prbt' : id+'t';
	document.getElementById(show_table).style.display = 'block';
	document.getElementById(id+'m').style.backgroundColor = 'white';
}

function show(id) {
	var el = document.getElementById(id);
	var sel = el.options[el.selectedIndex].value;
	var dth = d3.selectAll('.dth').style("display","none");
	var siti = d3.selectAll('.siti').style("display","none");
	var lin = d3.selectAll('.lin').style("display","none");
	if(sel=='Assumption') {
		document.getElementById('lin').value = '';
		dth.style("display","table-cell");
// 		var e = document.getElementById('dth');
// 		e.focus();
// 		e.value = 'Plus 1';
	} else if(sel == 'SI/TI') {
		siti.style("display","table-cell");
		lin.style("display","table-cell");
		// document.getElementById("siti").focus();
	} else if(sel!='--Select--' && sel!='Flag' && sel!='=I') {
		lin.style("display","inline");
		// document.getElementById("lin").focus();
	}
}

function exp(x) {
	var el = document.getElementById(x);
	var tr = document.getElementById(x+'trigger');
	var dic = {sync:'Symbols', srulc:'Rules for Sentential Logic', qrulc:'Rules for Quantificational Logic', drulc:'Derived Rules', exc: 'Examples'};
	if(el.style.display=='none' || el.style.display=='' ) {
		el.style.display = 'block';
		tr.innerHTML = '[–] '+dic[x];
	} else {
		el.style.display = 'none';
		tr.innerHTML = '[+] '+dic[x];
	}	
}