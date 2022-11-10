(* VDM to Isabelle Translation @2022-11-10T14:49:07.733Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultGuesser.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultGuesser.vdmsl]
*)
theory DefaultGuesser
imports "GLOBAL" "VDMToolkit" 
begin


\<comment>\<open>VDM source: DefaultGuess: (GuessHistory -> Coordinates)
	DefaultGuess(gh) ==
let c in set ALL_COORDINATES be st (c not in set (elems (gh.Coords))) in c\<close>
\<comment>\<open>in 'DefaultGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultGuesser.vdmsl) at line 8:1\<close>

\<comment>\<open>VDM source: pre_DefaultGuess: (GuessHistory +> bool)
	pre_DefaultGuess(gh) ==
null\<close>
\<comment>\<open>in 'DefaultGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultGuesser.vdmsl) at line 8:1\<close>
definition
	pre_DefaultGuess :: "GuessHistory \<Rightarrow> bool"
where
	"pre_DefaultGuess gh \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_DefaultGuess` specification.\<close>
		(inv_GuessHistory gh)"


\<comment>\<open>VDM source: post_DefaultGuess: (GuessHistory * Coordinates +> bool)
	post_DefaultGuess(gh, RESULT) ==
null\<close>
\<comment>\<open>in 'DefaultGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultGuesser.vdmsl) at line 8:1\<close>
definition
	post_DefaultGuess :: "GuessHistory \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"post_DefaultGuess gh   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultGuess` specification.\<close>
		(pre_DefaultGuess gh \<longrightarrow> (inv_GuessHistory gh  \<and>  inv_Coordinates RESULT))"

definition
	DefaultGuess :: "GuessHistory \<Rightarrow> Coordinates"
where
	"DefaultGuess gh \<equiv> 
	\<comment>\<open>User defined body of DefaultGuess.\<close>
	(
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>GLOBAL.ALL_COORDINATES))  \<and> (c \<notin> (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))) }))"



end