(* VDM to Isabelle Translation @2022-11-10T14:49:07.705Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl]
*)
theory ArrangingStrategy
imports "DefaultArranger" "DummyArranger" "Grid" "VDMToolkit" 
begin


\<comment>\<open>VDM source: ArngType = seq of (char)\<close>
\<comment>\<open>in 'ArrangingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl) at line 9:1\<close>
type_synonym ArngType = "VDMChar VDMSeq"
	

\<comment>\<open>VDM source: inv_ArngType: (ArngType +> bool)
	inv_ArngType(dummy0) ==
null\<close>
\<comment>\<open>in 'ArrangingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl) at line 9:1\<close>
definition
	inv_ArngType :: "ArngType \<Rightarrow> bool"
where
	"inv_ArngType dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_ArngType` specification.\<close>
		(((inv_VDMSeq' (inv_VDMChar) dummy0)))"
 
lemmas inv_ArngType_defs = inv_ArngType_def inv_VDMChar_def inv_VDMSeq'_def inv_VDMSeq'_defs 


	
	
\<comment>\<open>VDM source: Arrange: (ArngType -> Grid)
	Arrange(t) ==
(if (t = "DefaultArranger")
then DefaultArrange()
else (if (t = "DummyArranger")
then DummyArrange()
else DefaultArrange()))\<close>
\<comment>\<open>in 'ArrangingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl) at line 12:1\<close>

\<comment>\<open>VDM source: pre_Arrange: (ArngType +> bool)
	pre_Arrange(t) ==
null\<close>
\<comment>\<open>in 'ArrangingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl) at line 12:1\<close>
definition
	pre_Arrange :: "ArngType \<Rightarrow> bool"
where
	"pre_Arrange t \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Arrange` specification.\<close>
		((inv_ArngType t))"


\<comment>\<open>VDM source: post_Arrange: (ArngType * Grid +> bool)
	post_Arrange(t, RESULT) ==
null\<close>
\<comment>\<open>in 'ArrangingStrategy' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\ArrangingStrategy.vdmsl) at line 12:1\<close>
definition
	post_Arrange :: "ArngType \<Rightarrow> Grid \<Rightarrow> bool"
where
	"post_Arrange t   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Arrange` specification.\<close>
		(pre_Arrange t \<longrightarrow> ((inv_ArngType t)  \<and>  (inv_Grid RESULT)))"

definition
	Arrange :: "ArngType \<Rightarrow> Grid"
where
	"Arrange t \<equiv> 
	\<comment>\<open>User defined body of Arrange.\<close>
	(
		if ((t = (''DefaultArranger''))) then
		((DefaultArranger.DefaultArrange ))
		else
		((
		if ((t = (''DummyArranger''))) then
		((DummyArranger.DummyArrange ))
		else
		((DefaultArranger.DefaultArrange )))))"



end