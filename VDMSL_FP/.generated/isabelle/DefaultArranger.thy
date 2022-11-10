(* VDM to Isabelle Translation @2022-11-10T14:49:07.729Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl]
*)
theory DefaultArranger
imports "GLOBAL" "Grid" "Ship" "VDMToolkit" 
begin


\<comment>\<open>VDM source: ArrangeRecMeasure: (Grid * seq of (nat) -> nat)
	ArrangeRecMeasure(g, s) ==
(len s)\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 11:1\<close>

\<comment>\<open>VDM source: pre_ArrangeRecMeasure: (Grid * seq of (nat) +> bool)
	pre_ArrangeRecMeasure(g, s) ==
null\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 11:1\<close>
definition
	pre_ArrangeRecMeasure :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_ArrangeRecMeasure g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_ArrangeRecMeasure` specification.\<close>
		((inv_Grid g)  \<and>  (inv_VDMSeq' (inv_VDMNat) s))"


\<comment>\<open>VDM source: post_ArrangeRecMeasure: (Grid * seq of (nat) * nat +> bool)
	post_ArrangeRecMeasure(g, s, RESULT) ==
null\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 11:1\<close>
definition
	post_ArrangeRecMeasure :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_ArrangeRecMeasure g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ArrangeRecMeasure` specification.\<close>
		(pre_ArrangeRecMeasure g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_VDMSeq' (inv_VDMNat) s)  \<and>  (inv_VDMNat RESULT)))"

definition
	ArrangeRecMeasure :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMNat"
where
	"ArrangeRecMeasure g   s \<equiv> 
	\<comment>\<open>User defined body of ArrangeRecMeasure.\<close>
	(len s)"

	
	
\<comment>\<open>VDM source: ArrangeRec: (Grid * seq of (nat) -> Grid)
	ArrangeRec(g, s) ==
(if (s = [])
then g
else let l:nat = (hd s), combinations:set of ((bool * Coordinates)) = {mk_(d, c) | d in set {true, false}, c in set ALL_COORDINATES} in let mk_(d, c) in set combinations be st PlaceableShip(g, MakeShip(c, (if d
then mk_GLOBAL`Coordinates((((c.X) + l) - 1), (c.Y))
else mk_GLOBAL`Coordinates((c.X), (((c.Y) + l) - 1))))) in ArrangeRec(PlaceShip(g, MakeShip(c, (if d
then mk_GLOBAL`Coordinates((((c.X) + l) - 1), (c.Y))
else mk_GLOBAL`Coordinates((c.X), (((c.Y) + l) - 1))))), (tl s)))
	measure ArrangeRecMeasure\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 14:1\<close>

\<comment>\<open>VDM source: pre_ArrangeRec: (Grid * seq of (nat) +> bool)
	pre_ArrangeRec(g, s) ==
null\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 14:1\<close>
definition
	pre_ArrangeRec :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_ArrangeRec g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_ArrangeRec` specification.\<close>
		((inv_Grid g)  \<and>  (inv_VDMSeq' (inv_VDMNat) s))"


\<comment>\<open>VDM source: post_ArrangeRec: (Grid * seq of (nat) * Grid +> bool)
	post_ArrangeRec(g, s, RESULT) ==
null\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 14:1\<close>
definition
	post_ArrangeRec :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> Grid \<Rightarrow> bool"
where
	"post_ArrangeRec g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ArrangeRec` specification.\<close>
		(pre_ArrangeRec g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_VDMSeq' (inv_VDMNat) s)  \<and>  (inv_Grid RESULT)))"

fun
	ArrangeRec :: "Grid \<Rightarrow> VDMNat VDMSeq \<Rightarrow> Grid"
where
	"ArrangeRec g   s = 
	\<comment>\<open>User defined body of ArrangeRec.\<close>
	(
		if ((s = [])) then
		(g)
		else
		((
		let 
(l::VDMNat) = (hd s)
		;
		
(combinations::(bool \<times> Coordinates) VDMSet) = { (d , c) | d  c .  ((d \<in>{(True::\<bool>) , (False::\<bool>)}))  \<and>  ((c \<in>GLOBAL.ALL_COORDINATES))  }
		in
			
			(if ((inv_VDMNat l))
	 \<and> 
	((inv_VDMSet' 
		(\<lambda> (dummy1of2, dummy2of2) . (inv_bool dummy1of2)\<and>
		  (((inv_VDMNat (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s dummy2of2))) \<and> 
		 ((inv_VDMNat (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s dummy2of2))) )
		) combinations)) then
			(
		SOME (dummy0::Grid) .(dummy0 \<in> { (\<comment>\<open>Implicit pattern context projection for `pattern list`\<close>
	 let d = (fst dummy0); c = (snd dummy0) in (ArrangeRec (Grid.PlaceShip g  (Ship.MakeShip c  ( if (d) then (\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + l) - (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr>) else (\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + l) - (1::VDMNat1))\<rparr>))))  (tl s))) | dummy0 .  ((dummy0 \<in>combinations))  \<and> (\<comment>\<open>Implicit pattern context projection for `pattern list`\<close>
	 let d = (fst dummy0); c = (snd dummy0) in (Grid.PlaceableShip g  (Ship.MakeShip c  ( if (d) then (\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + l) - (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr>) else (\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + l) - (1::VDMNat1))\<rparr>))))) }))
		 else
			undefined
		)
		)))"

	
	
\<comment>\<open>VDM source: DefaultArrange: (() -> Grid)
	DefaultArrange() ==
ArrangeRec([], SHIPS_BY_LEN)
	post ((len RESULT) = (len SHIPS_BY_LEN))\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 29:1\<close>

\<comment>\<open>VDM source: pre_DefaultArrange: (() +> bool)
	pre_DefaultArrange() ==
null\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 29:1\<close>
definition
	pre_DefaultArrange :: "bool"
where
	"pre_DefaultArrange  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultArrange: (Grid +> bool)
	post_DefaultArrange(RESULT) ==
((len RESULT) = (len SHIPS_BY_LEN))\<close>
\<comment>\<open>in 'DefaultArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DefaultArranger.vdmsl) at line 31:17\<close>
definition
	post_DefaultArrange :: "Grid \<Rightarrow> bool"
where
	"post_DefaultArrange RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_DefaultArrange` specification.\<close>
		(pre_DefaultArrange  \<longrightarrow> ((inv_Grid RESULT)))  \<and> 
		\<comment>\<open>User defined body of post_DefaultArrange.\<close>
		((len RESULT) = (len GLOBAL.SHIPS_BY_LEN))"

definition
	DefaultArrange :: "Grid"
where
	"DefaultArrange  \<equiv> 
	\<comment>\<open>User defined body of DefaultArrange.\<close>
	(ArrangeRec []  GLOBAL.SHIPS_BY_LEN)"



end