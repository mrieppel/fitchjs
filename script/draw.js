var FW = 20, // width between fitch bars
	LH = 30, // height between proof lines
	NW = 30, // width of numbering column
	OS = LH/6, // offset for text (above baseline and right of fitch bar)
	RC = 30; // space between formula and rule

function draw() {
	var SVGW = "100%",
		SVGH = LH;
		
	if(PROOF.length > 0) {	
		var max = d3.max(PROOF, function(d) {return d.rul=="Premise" ? d.cnt : 0;}); // line number of last premise
		SVGH = PROOF.length*LH;
	}
	var proof = d3.select("#drv")
		.attr("width", SVGW)
		.attr("height", SVGH);

	var line = proof.selectAll("g")
		.data(PROOF);


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
						return "M"+((i*FW)+NW)+" 0 V "+LH;
					});
			}
			var x = ((d.dth-1)*FW)+NW;
			el.append("path") // adds last fitch line 
				.attr("d",function(d) {
					return "M"+x+" "+(pflag ? 0 : (1.6*OS))+" V "+LH;
				});
			el.append("path") // adds horizontal assumption line
				.attr("d",function(d) {
					return "M"+x+" "+LH+" H "+(x+10);
				});
		} else { // adds fitch lines for non-assumption lines
			for(var i=0;i<=(d.dth-1);i++) {
				el.append("path")
					.attr("d", function(d) {
						return "M"+((i*FW)+NW)+" 0 V "+LH;
					});
			}
		}
	});

	l.append("text") // append line number
		.attr("x","0")
		.attr("y",""+(LH-OS))
		.text(function(d) {return d.cnt;});

	l.append("text") // append formula
		.attr("x", function(d) {return NW+(FW*(d.dth>1 ? d.dth-1 : 0))+(d.dth>0 ? OS : 0);})
		.attr("y", ""+(LH-OS))
		.attr("class","dfrm")
		.attr("id",function(d) {return "frm"+d.cnt;})
		.text(function(d) {return padBCs(richardify(d.frm));});

	l.append("text") // append rule
		.attr("class","drul")
		.text(function(d) {return linD(d.lin)+" "+gRul(d.rul);});

	l.append("text") // append line delete
		.attr("class","del");
	 
	line.exit().remove();	
	
	if(PROOF.length) {
		var wf = d3.max(d3.selectAll(".dfrm")[0], function(d) {
			var e = d3.select(d);
			var box = e.node().getBBox();
			return box["width"]+box["x"];})
		d3.selectAll('.drul')
			.attr("x",wf+RC)
			.attr("y",(LH-OS));
		var wr = d3.max(d3.selectAll(".drul")[0], function(d) {
			var e = d3.select(d);
			var box = e.node().getBBox();
			return box["width"]+box["x"];})
		d3.selectAll(".del")
			.attr("x",wr+FW)
			.attr("y",(LH-OS))
			.html(function(d) {return d.cnt>max && d.cnt==PROOF.length ? "&#x2717" : "";})
			.on("click",function() {clrlast();});	
	}	
}

function draw_goals() {
	var SVG2W = "100%",
		SVG2H = 0;
	if(GOALS.length) {
		SVG2H = GOALS.length*LH;
	}		
		
	var goals = d3.select("#gls")
 		.attr("width", SVG2W)
 		.attr("height", SVG2H);
	
	var goal = goals.selectAll("g")
		.data(GOALS);
		
	goal.select(".glfrm").text(function(d) {return padBCs(richardify(d));});
	
	var g = goal.enter().append("g");
	
	g.attr("transform",function(d,i) {return "translate(0,"+(i*LH)+")";});
		
	g.append("text")
		.attr("x",0)
		.attr("y",""+(LH-OS))
		.attr("class","gllbl")
		.text("Goal:");
	
	g.append("text")
		.attr("class","glfrm")
		.text(function(d) {return richardify(d);});
	
	g.append("text")
		.attr("class","gdel");
	
	goal.exit().remove();
	
	if(CONCLUSION.length) {
		var box = d3.select("#conlbl").node().getBBox();
		var w = box["width"];
		d3.selectAll('.glfrm')
			.attr("x",w+10)
			.attr("y",(LH-OS));
	}
	
	var wf = d3.max(d3.selectAll(".glfrm")[0], function(d) {
		var e = d3.select(d);
		var box = e.node().getBBox();
		return box["width"]+box["x"];})
	d3.selectAll(".gdel")
		.attr("x",wf+FW)
		.attr("y",(LH-OS))
		.html(function(d,i) {return i==0 ? "&#x2717" : "";})
		.on("click",function() {delete_goal();});
}

function draw_conclusion() {
	var el = d3.select("#con")
		.attr("width", "100%")
		.attr("height",LH);
	
	var con = el.selectAll("g")
		.data(CONCLUSION);	
	
	con.enter()
		.append("g")
		.attr("transform","translate(0,0)")
		.attr("id","g");
		
	con.append("text")
		.attr("x",0)
		.attr("y",""+(LH-OS))
		.attr("id","conlbl")
		.text("Conclusion:");
	
	con.append("text")
		.attr("id","confrm")
		.text(function(d) {return padBCs(richardify(d));});
	
	con.exit().remove();
	
	if(CONCLUSION.length) {
		var box = d3.select("#conlbl").node().getBBox();
		var w = box["width"];
		d3.select("#confrm")
			.attr("x",10+w)
			.attr("y",(LH-OS));
	};	

}