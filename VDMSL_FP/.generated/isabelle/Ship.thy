(* VDM to Isabelle Translation @2022-11-10T14:49:07.793Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl]
*)
theory Ship
imports "GLOBAL" "VDMToolkit" 
begin


\<comment>\<open>VDM source: Ship = compose Ship of Coords:seq1 of (Coordinates), Hit:seq1 of (bool), Length:nat end
	inv s == (((len (s.Coords)) = (card (elems (s.Coords)))) and (((len (s.Coords)) = (len (s.Hit))) and (forall c1, c2 in set (elems (s.Coords)) & ((((c1.X) = (c2.X)) and (((c1.Y) < (c2.Y)) => ({(c1.Y), ... ,(c2.Y)} subset Ycoords((elems (s.Coords)))))) or (((c1.Y) = (c2.Y)) and (((c1.X) < (c2.X)) => ({(c1.X), ... ,(c2.X)} subset Xcoords((elems (s.Coords))))))))))\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 7:1\<close>
record Ship =  Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p :: "Coordinates VDMSeq1"
		 
		 Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p :: "bool VDMSeq1"
		 
		 Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p :: "VDMNat" 

\<comment>\<open>VDM source: inv_Ship: (Ship +> bool)
	inv_Ship(s) ==
(((len (s.Coords)) = (card (elems (s.Coords)))) and (((len (s.Coords)) = (len (s.Hit))) and (forall c1, c2 in set (elems (s.Coords)) & ((((c1.X) = (c2.X)) and (((c1.Y) < (c2.Y)) => ({(c1.Y), ... ,(c2.Y)} subset Ycoords((elems (s.Coords)))))) or (((c1.Y) = (c2.Y)) and (((c1.X) < (c2.X)) => ({(c1.X), ... ,(c2.X)} subset Xcoords((elems (s.Coords))))))))))\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 12:5\<close>
definition
	inv_Ship :: "Ship \<Rightarrow> bool"
where
	"inv_Ship s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Ship` specification.\<close>
		( (((inv_VDMSeq1' inv_Coordinates  (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))) \<and> 
		 ((inv_VDMSeq1' (inv_bool) (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))) \<and> 
		 ((inv_VDMNat (Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))) ))  \<and> 
		\<comment>\<open>User defined body of inv_Ship.\<close>
		(((len (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)) = (vdm_card (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)))) \<and> (((len (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)) = (len (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))) \<and> (\<forall> c1 \<in> (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))  . (\<forall> c2 \<in> (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))  . ((((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<and> (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) < (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<longrightarrow> ({(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)} \<subseteq> (GLOBAL.Ycoords (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)))))) \<or> (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<and> (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) < (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<longrightarrow> ({(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)} \<subseteq> (GLOBAL.Xcoords (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)))))))))))"
 
lemmas inv_Ship_defs = inv_Coordinates_def inv_Ship_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: MakeShip: (Coordinates * Coordinates -> Ship)
	MakeShip(cStart, cEnd) ==
(if ((cStart.X) = (cEnd.X))
then mk_Ship([mk_GLOBAL`Coordinates((cStart.X), Y) | Y in set {(cStart.Y), ... ,(cEnd.Y)}], [false | Y in set {(cStart.Y), ... ,(cEnd.Y)}], (((cEnd.Y) - (cStart.Y)) + 1))
else mk_Ship([mk_GLOBAL`Coordinates(X, (cStart.Y)) | X in set {(cStart.X), ... ,(cEnd.X)}], [false | X in set {(cStart.X), ... ,(cEnd.X)}], (((cEnd.X) - (cStart.X)) + 1)))
	pre ((((cStart.X) = (cEnd.X)) or ((cStart.Y) = (cEnd.Y))) and (((cStart.X) <= (cEnd.X)) and ((cStart.Y) <= (cEnd.Y))))\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 19:1\<close>

\<comment>\<open>VDM source: pre_MakeShip: (Coordinates * Coordinates +> bool)
	pre_MakeShip(cStart, cEnd) ==
((((cStart.X) = (cEnd.X)) or ((cStart.Y) = (cEnd.Y))) and (((cStart.X) <= (cEnd.X)) and ((cStart.Y) <= (cEnd.Y))))\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 29:5\<close>
definition
	pre_MakeShip :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"pre_MakeShip cStart   cEnd \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_MakeShip` specification.\<close>
		(inv_Coordinates cStart  \<and>  inv_Coordinates cEnd)  \<and> 
		\<comment>\<open>User defined body of pre_MakeShip.\<close>
		((((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart) = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)) \<or> ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart) = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd))) \<and> (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart) \<le> (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)) \<and> ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart) \<le> (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd))))"


\<comment>\<open>VDM source: post_MakeShip: (Coordinates * Coordinates * Ship +> bool)
	post_MakeShip(cStart, cEnd, RESULT) ==
null\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 19:1\<close>
definition
	post_MakeShip :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> Ship \<Rightarrow> bool"
where
	"post_MakeShip cStart   cEnd   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_MakeShip` specification.\<close>
		(pre_MakeShip cStart  cEnd \<longrightarrow> (inv_Coordinates cStart  \<and>  inv_Coordinates cEnd  \<and>  inv_Ship RESULT))"

definition
	MakeShip :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> Ship"
where
	"MakeShip cStart   cEnd \<equiv> 
	\<comment>\<open>User defined body of MakeShip.\<close>
	(
		if (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart) = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd))) then
		(\<lparr>Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p = [ \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = Y\<rparr> . Y \<leftarrow> sorted_list_of_set ({(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)}) , ((Y \<in>{(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)})) ], Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p = [ (False::\<bool>) . Y \<leftarrow> sorted_list_of_set ({(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)}) , ((Y \<in>{(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)})) ], Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p = (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd) - (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)) + (1::VDMNat1))\<rparr>)
		else
		(\<lparr>Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p = [ \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = X, Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)\<rparr> . X \<leftarrow> sorted_list_of_set ({(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)}) , ((X \<in>{(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)})) ], Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p = [ (False::\<bool>) . X \<leftarrow> sorted_list_of_set ({(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)}) , ((X \<in>{(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd)})) ], Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p = (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cEnd) - (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s cStart)) + (1::VDMNat1))\<rparr>))"

	
	
\<comment>\<open>VDM source: HitShip: (Ship * Coordinates -> (Ship * GuessResult))
	HitShip(s, coord) ==
let i in set (inds (s.Coords)) be st ((s.Coords)(i) = coord) in let postHit:Ship = mk_Ship((s.Coords), (SeqReplaceAt)[bool]((s.Hit), true, i), (s.Length)) in mk_(postHit, mk_GLOBAL`GuessResult(true, ((elems (postHit.Hit)) = {true})))
	pre ((elems (s.Hit)) <> {true})\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 31:1\<close>

\<comment>\<open>VDM source: pre_HitShip: (Ship * Coordinates +> bool)
	pre_HitShip(s, coord) ==
((elems (s.Hit)) <> {true})\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 38:17\<close>
definition
	pre_HitShip :: "Ship \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"pre_HitShip s   coord \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_HitShip` specification.\<close>
		(inv_Ship s  \<and>  inv_Coordinates coord)  \<and> 
		\<comment>\<open>User defined body of pre_HitShip.\<close>
		((elems (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)) \<noteq> {(True::\<bool>)})"


\<comment>\<open>VDM source: post_HitShip: (Ship * Coordinates * (Ship * GuessResult) +> bool)
	post_HitShip(s, coord, RESULT) ==
null\<close>
\<comment>\<open>in 'Ship' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Ship.vdmsl) at line 31:1\<close>
definition
	post_HitShip :: "Ship \<Rightarrow> Coordinates \<Rightarrow> (Ship \<times> GuessResult) \<Rightarrow> bool"
where
	"post_HitShip s   coord   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_HitShip` specification.\<close>
		(pre_HitShip s  coord \<longrightarrow> (inv_Ship s  \<and>  inv_Coordinates coord  \<and>  
		(inv_Ship (fst RESULT)\<and>
		 inv_GuessResult (snd RESULT)
		)))"

definition
	HitShip :: "Ship \<Rightarrow> Coordinates \<Rightarrow> (Ship \<times> GuessResult)"
where
	"HitShip s   coord \<equiv> 
	\<comment>\<open>User defined body of HitShip.\<close>
	(
		SOME (dummy0::(Ship \<times> GuessResult)) .(dummy0 \<in> { (
		let 
(postHit::Ship) = \<lparr>Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p = (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s), Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p = (GLOBAL.SeqReplaceAt (inv_bool)  (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)  (True::\<bool>)  i), Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p = (Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)\<rparr>
		in
			
			(if (inv_Ship  postHit) then
			(postHit , \<lparr>Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (True::\<bool>), Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = ((elems (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p postHit)) = {(True::\<bool>)})\<rparr>)
		 else
			undefined
		)
		) | i .  ((i \<in>(inds (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))))  \<and> (((Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)$i) = coord) }))"



end