Fitch
=====

This program provides a web interface for users to construct proofs in a Fitch-style natural deduction system.  It is a modification of the LemmoNaDe program, and implements a similar rule set (based on the rules in [Graeme Forbes'](http://www.colorado.edu/philosophy/fac_forbes.shtml) textbook [Modern Logic](http://www.amazon.com/Modern-Logic-Text-Elementary-Symbolic/dp/0195080297)). The fitch proofs are drawn using the [D3.js](http://d3js.org/) library.  This program has not been extensively tested, so it likely still contains some bugs.  If you come across one, please let me know!

A live version of the program is [here](http://mrieppel.github.io/fitch/).

Here's a brief description of the content of the various javascript files:

* `script/draw.js`: code to draw the proof as an svg using D3.js.

* `script/parsing.js`: code to parse formulas into trees.  Also contains code for transforming formulas in the "plain" notation into formulas containing unicode characters, and code for generating formulas in latex.  Note that internally, the program expects the "simple" notation, e.g. '>' and '<>', rather than the unicode variants.  Proofs can also only be imported in the plain notation.

* `script/rules_helper.js`: various helper functions needed by the rule checking code. E.g. checking what lines are available from the current line, checking what free variables occur in a line, creating instances of quantified formulas etc.

* `script/rules_pl.js`: code implementing rules of propositional logic.

* `script/rules_ql.js`: code implementing rules of quantificational logic.

* `script/rules_siti_pl.js`: code implementing sequent/theorem introduction (SI/TI) rules.

* `samples/`: contains some sample proofs that can be imported into the program.  The program will export proofs in LaTex format that compiles using Johan Klüwer's fitch.sty (also included).

* `script/ui.js`: code for the user interface, i.e. to dynamically change which menu item ("Construct Proof", "Export/Import", and "Reference") the user sees as active.

* `script/userio.js`: code to capture user input (e.g. to begin a problem, append a line, import a proof etc.) and generate the appropriate output to the html page.  Also contains the global variable that holds the proof.

* `script/validate.js`: code to validate the user input, e.g. checking for well-formedness of input formulas, and to dispatch the user input to the appropriate rule checking code.