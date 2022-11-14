(* VDM to Isabelle Translation @2022-11-14T10:32:19.063Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl]
*)
theory DummyArranger
imports "GLOBAL" "Grid" "Ship" "VDMToolkit" 
begin


\<comment>\<open>VDM source: DummyArrangeRecMeasure: (Grid * Grid -> nat)
	DummyArrangeRecMeasure(g, s) ==
(len s)\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 15:1\<close>

\<comment>\<open>VDM source: pre_DummyArrangeRecMeasure: (Grid * Grid +> bool)
	pre_DummyArrangeRecMeasure(g, s) ==
null\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 15:1\<close>
definition
	pre_DummyArrangeRecMeasure :: "Grid \<Rightarrow> Grid \<Rightarrow> bool"
where
	"pre_DummyArrangeRecMeasure g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_DummyArrangeRecMeasure` specification.\<close>
		((inv_Grid g)  \<and>  (inv_Grid s))"


\<comment>\<open>VDM source: post_DummyArrangeRecMeasure: (Grid * Grid * nat +> bool)
	post_DummyArrangeRecMeasure(g, s, RESULT) ==
null\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 15:1\<close>
definition
	post_DummyArrangeRecMeasure :: "Grid \<Rightarrow> Grid \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_DummyArrangeRecMeasure g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DummyArrangeRecMeasure` specification.\<close>
		(pre_DummyArrangeRecMeasure g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_Grid s)  \<and>  (inv_VDMNat RESULT)))"

definition
	DummyArrangeRecMeasure :: "Grid \<Rightarrow> Grid \<Rightarrow> VDMNat"
where
	"DummyArrangeRecMeasure g   s \<equiv> 
	\<comment>\<open>User defined body of DummyArrangeRecMeasure.\<close>
	(len s)"

	
	
\<comment>\<open>VDM source: DummyArrangeRec: (Grid * Grid -> Grid)
	DummyArrangeRec(g, s) ==
(if (s = [])
then g
else (if PlaceableShip(g, (hd s))
then DummyArrangeRec(PlaceShip(g, (hd s)), (tl s))
else g))
	measure DummyArrangeRecMeasure\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 18:1\<close>

\<comment>\<open>VDM source: pre_DummyArrangeRec: (Grid * Grid +> bool)
	pre_DummyArrangeRec(g, s) ==
null\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 18:1\<close>
definition
	pre_DummyArrangeRec :: "Grid \<Rightarrow> Grid \<Rightarrow> bool"
where
	"pre_DummyArrangeRec g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_DummyArrangeRec` specification.\<close>
		((inv_Grid g)  \<and>  (inv_Grid s))"


\<comment>\<open>VDM source: post_DummyArrangeRec: (Grid * Grid * Grid +> bool)
	post_DummyArrangeRec(g, s, RESULT) ==
null\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 18:1\<close>
definition
	post_DummyArrangeRec :: "Grid \<Rightarrow> Grid \<Rightarrow> Grid \<Rightarrow> bool"
where
	"post_DummyArrangeRec g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DummyArrangeRec` specification.\<close>
		(pre_DummyArrangeRec g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_Grid s)  \<and>  (inv_Grid RESULT)))"

fun
	DummyArrangeRec :: "Grid \<Rightarrow> Grid \<Rightarrow> Grid"
where
	"DummyArrangeRec g   s = 
	\<comment>\<open>User defined body of DummyArrangeRec.\<close>
	(
		if ((s = [])) then
		(g)
		else
		((
		if ((Grid.PlaceableShip g  (hd s))) then
		((DummyArrangeRec (Grid.PlaceShip g  (hd s))  (tl s)))
		else
		(g))))"

	
	
\<comment>\<open>VDM source: DummyArrange: (() -> Grid)
	DummyArrange() ==
let s1:Ship = MakeShip(mk_GLOBAL`Coordinates(2, 1), mk_GLOBAL`Coordinates(5, 1)), s2:Ship = MakeShip(mk_GLOBAL`Coordinates(1, 1), mk_GLOBAL`Coordinates(1, 3)), s3:Ship = MakeShip(mk_GLOBAL`Coordinates(3, 3), mk_GLOBAL`Coordinates(3, 4)), s4:Ship = MakeShip(mk_GLOBAL`Coordinates(2, 4), mk_GLOBAL`Coordinates(2, 5)) in DummyArrangeRec([], [s1, s2, s3, s4])
	post ((len RESULT) = (len SHIPS_BY_LEN))\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 25:1\<close>

\<comment>\<open>VDM source: pre_DummyArrange: (() +> bool)
	pre_DummyArrange() ==
null\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 25:1\<close>
definition
	pre_DummyArrange :: "bool"
where
	"pre_DummyArrange  \<equiv> True"


\<comment>\<open>VDM source: post_DummyArrange: (Grid +> bool)
	post_DummyArrange(RESULT) ==
((len RESULT) = (len SHIPS_BY_LEN))\<close>
\<comment>\<open>in 'DummyArranger' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\DummyArranger.vdmsl) at line 33:17\<close>
definition
	post_DummyArrange :: "Grid \<Rightarrow> bool"
where
	"post_DummyArrange RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_DummyArrange` specification.\<close>
		(pre_DummyArrange  \<longrightarrow> ((inv_Grid RESULT)))  \<and> 
		\<comment>\<open>User defined body of post_DummyArrange.\<close>
		((len RESULT) = (len GLOBAL.SHIPS_BY_LEN))"

definition
	DummyArrange :: "Grid"
where
	"DummyArrange  \<equiv> 
	\<comment>\<open>User defined body of DummyArrange.\<close>
	(
		let 
(s1::Ship) = (Ship.MakeShip \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (2::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (1::VDMNat1)\<rparr>  \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (5::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (1::VDMNat1)\<rparr>)
		;
		
(s2::Ship) = (Ship.MakeShip \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (1::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (1::VDMNat1)\<rparr>  \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (1::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (3::VDMNat1)\<rparr>)
		;
		
(s3::Ship) = (Ship.MakeShip \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (3::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (3::VDMNat1)\<rparr>  \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (3::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (4::VDMNat1)\<rparr>)
		;
		
(s4::Ship) = (Ship.MakeShip \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (2::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (4::VDMNat1)\<rparr>  \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (2::VDMNat1), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (5::VDMNat1)\<rparr>)
		in
			
			(if (inv_Ship  s1)
	 \<and> 
	(inv_Ship  s2)
	 \<and> 
	(inv_Ship  s3)
	 \<and> 
	(inv_Ship  s4) then
			(DummyArrangeRec []  [s1 , s2 , s3 , s4])
		 else
			undefined
		)
		)"



end