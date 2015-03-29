var FW = 20, // width between fitch bars
	LH = 30, // height between proof lines
	NW = 40, // width of numbering column
	OS = LH/6; // offset for text (above baseline and right of fitch bar)

function draw() {
	var RC = 0,
		SVGW = 300,
		SVGH = 30;
		
	if(PROOF.length > 0) {
		var fl = d3.max(PROOF, function(d) {return d.frm.length;});
		var RC = 	NW + (fl*14) + OS +
					((d3.max(PROOF, function(d) {return d.dth;})) *
					FW); // horizontal distance from origin of rule column			
		var max = d3.max(PROOF, function(d) { return d.rul=="Premise" ? d.cnt : 0;}); // line number of last premise
	
		var SVGW = RC+(14*d3.max(PROOF,function(d) {return d.rul.length;}));
			SVGH = PROOF.length*LH;
	}
	var proof = d3.select("#drv")
		.attr("width", SVGW)
		.attr("height", SVGH);

	var line = proof.selectAll("g")
		.data(PROOF);

	line.selectAll('.rulc')
		.attr("x", RC)
		.attr("y",(LH-OS))

	var l = line.enter()
		.append("g")
		.attr("transform",function(d,i) {return "translate(0," + i*LH + ")";});

	l.each(function(d,i) { // draw fitch lines
		var el = d3.select(this);
		var pflag = (d.rul=="Premise") && (d.cnt == max);	
		if(d.rul=="Assumption" || pflag || d.rul=='Flag') { // adds fitch lines for assumption lines
			for(var i=0;i<(d.dth-1);i++) {
				el.append("path")
					.attr("d",function(d) {
						return "M"+((i*FW)+NW)+" 0, V "+LH;
					});
			}
			var x = ((d.dth-1)*FW)+NW;
			el.append("path") // adds last fitch line 
				.attr("d",function(d) {
					return "M"+x+" "+(pflag ? 0 : (1.6*OS))+", V "+LH;
				});
			el.append("path") // adds horizontal assumption line
				.attr("d",function(d) {
					return "M"+x+" "+LH+", H "+(x+10);
				});
		} else { // adds fitch lines for non-assumption lines
			for(var i=0;i<=(d.dth-1);i++) {
				el.append("path")
					.attr("d", function(d) {
						return "M"+((i*FW)+NW)+" 0, V "+LH;
					});
			}
		}
	});

	l.append("text") // append line number
		.attr("x","0")
		.attr("y",""+(LH-OS))
		.text(function(d) {return d.cnt;});

	l.append("text") // append formula
		.attr("x", function(d) {return NW+(FW*(d.dth > 1 ? d.dth-1 : 0))+OS;})
		.attr("y", ""+(LH-OS))
		.text(function(d) {return padBCs(richardify(d.frm));});

	l.append("text") // append rule
		.attr("x", RC)
		.attr("y",(LH-OS))
		.attr("class","rulc")
		.text(function(d) {return d.lin.join(',')+" "+gRul(d.rul);});
	
	line.exit().remove();	
}

function draw_goals() {

	var n = ("Conclusion".length*10);
	var SVG2W = 300,
		SVG2H = 0;
	if(GOALS.length) {	
		SVG2W = n+(10*d3.max(GOALS, function(d) {return d.length;}));
		SVG2H = GOALS.length*LH;
	}		
		
	var goals = d3.select("#gls")
 		.attr("width", SVG2W)
 		.attr("height", SVG2H);
	
	var goal = goals.selectAll("g")
		.data(GOALS);
		
	goal.select(".goalf").text(function(d) {return padBCs(richardify(d));});
	
	var g = goal.enter().append("g");
	
	g.attr("transform",function(d,i) {return "translate(0,"+(i*LH)+")";});
		
	g.append("text")
		.attr("x",0)
		.attr("y",""+(LH-OS))
		.text("Goal:");
	
	g.append("text")
		.attr("x",n)
		.attr("y",""+(LH-OS))
		.attr("class","goalf")
		.text(function(d) {return richardify(d);});
	
	goal.exit().remove();
}

function draw_conclusion() {
	var n = ("Conclusion".length*10);
	
	var SVG3W = 300,
		SVG3H = 0;
	if(CONCLUSION.length) {	
		SVG3W = n+(10*CONCLUSION[0].length),
		SVG3H = LH;
	}	
	
	var el = d3.select("#con")
 		.attr("width", SVG3W)
 		.attr("height", SVG3H);
	
	var con = el.selectAll("g")
		.data(CONCLUSION);	
	
	con.enter()
		.append("g")
		.attr("transform","translate(0,0)");
		
	con.append("text")
		.attr("x",0)
		.attr("y",""+(LH-OS))
		.text("Conclusion:");
	
	con.append("text")
		.attr("x",n)
		.attr("y",""+(LH-OS))
		.text(function(d) {return padBCs(richardify(d));});
	
	con.exit().remove();
}