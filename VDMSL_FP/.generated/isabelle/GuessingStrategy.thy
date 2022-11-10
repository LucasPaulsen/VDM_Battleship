(* VDM to Isabelle Translation @2022-11-10T14:49:07.774Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl]
*)
theory GuessingStrategy
imports "DefaultGuesser" "GLOBAL" "SearchGuesser" "VDMToolkit" 
begin


\<comment>\<open>VDM source: GuesType = seq of (char)\<close>
\<comment>\<open>in 'GuessingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl) at line 9:1\<close>
type_synonym GuesType = "VDMChar VDMSeq"
	

\<comment>\<open>VDM source: inv_GuesType: (GuesType +> bool)
	inv_GuesType(dummy0) ==
null\<close>
\<comment>\<open>in 'GuessingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl) at line 9:1\<close>
definition
	inv_GuesType :: "GuesType \<Rightarrow> bool"
where
	"inv_GuesType dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_GuesType` specification.\<close>
		(((inv_VDMSeq' (inv_VDMChar) dummy0)))"
 
lemmas inv_GuesType_defs = inv_GuesType_def inv_VDMChar_def inv_VDMSeq'_def inv_VDMSeq'_defs 


	
	
\<comment>\<open>VDM source: Guess: (GuesType * GuessHistory -> Coordinates)
	Guess(t, gh) ==
(if (t = "DefaultGuesser")
then DefaultGuess(gh)
else (if (t = "SearchGuesser")
then SearchGuess(gh)
else DefaultGuess(gh)))\<close>
\<comment>\<open>in 'GuessingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl) at line 12:1\<close>

\<comment>\<open>VDM source: pre_Guess: (GuesType * GuessHistory +> bool)
	pre_Guess(t, gh) ==
null\<close>
\<comment>\<open>in 'GuessingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl) at line 12:1\<close>
definition
	pre_Guess :: "GuesType \<Rightarrow> GuessHistory \<Rightarrow> bool"
where
	"pre_Guess t   gh \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Guess` specification.\<close>
		((inv_GuesType t)  \<and>  inv_GuessHistory gh)"


\<comment>\<open>VDM source: post_Guess: (GuesType * GuessHistory * Coordinates +> bool)
	post_Guess(t, gh, RESULT) ==
null\<close>
\<comment>\<open>in 'GuessingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GuessingStrategy.vdmsl) at line 12:1\<close>
definition
	post_Guess :: "GuesType \<Rightarrow> GuessHistory \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"post_Guess t   gh   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Guess` specification.\<close>
		(pre_Guess t  gh \<longrightarrow> ((inv_GuesType t)  \<and>  inv_GuessHistory gh  \<and>  inv_Coordinates RESULT))"

definition
	Guess :: "GuesType \<Rightarrow> GuessHistory \<Rightarrow> Coordinates"
where
	"Guess t   gh \<equiv> 
	\<comment>\<open>User defined body of Guess.\<close>
	(
		if ((t = (''DefaultGuesser''))) then
		((DefaultGuesser.DefaultGuess gh))
		else
		((
		if ((t = (''SearchGuesser''))) then
		((SearchGuesser.SearchGuess gh))
		else
		((DefaultGuesser.DefaultGuess gh)))))"



end