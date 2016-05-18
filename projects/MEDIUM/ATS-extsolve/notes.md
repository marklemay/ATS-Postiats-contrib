
Directory structure?

* what is the empty file CATS/ for?
* CNSTRNT/ converts the syntax elements to strings also to pretty printing
* PARSING parses from json 


See also my notes for https://github.com/marklemay/ATS-Postiats-contrib/tree/master/projects/MEDIUM/ATS-extsolve-z3


what code solves the linear constraints?


I think the 
```
local
  #include "./SOLVING/patsolve_z3_solving_ctx.dats"
in
  // nothing
end
```
pattern includes the raw file text in a seperate local scope
