(* VDM to Isabelle Translation @2022-11-10T14:49:07.757Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl]
*)
theory Grid
imports "GLOBAL" "Ship" "VDMToolkit" 
begin


\<comment>\<open>VDM source: ShipT = Ship\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 12:1\<close>
type_synonym ShipT = "Ship"
	

\<comment>\<open>VDM source: inv_ShipT: (ShipT +> bool)
	inv_ShipT(dummy0) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 12:1\<close>
definition
	inv_ShipT :: "ShipT \<Rightarrow> bool"
where
	"inv_ShipT dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_ShipT` specification.\<close>
		((inv_Ship dummy0))"
 
lemmas inv_ShipT_defs = inv_Coordinates_def inv_Ship_def inv_ShipT_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: Grid = seq of (ShipT)\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 14:1\<close>
type_synonym Grid = "ShipT VDMSeq"
	

\<comment>\<open>VDM source: inv_Grid: (Grid +> bool)
	inv_Grid(dummy0) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 14:1\<close>
definition
	inv_Grid :: "Grid \<Rightarrow> bool"
where
	"inv_Grid dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Grid` specification.\<close>
		(((inv_VDMSeq' inv_Ship dummy0)))"
 
lemmas inv_Grid_defs = inv_Coordinates_def inv_Grid_def inv_Ship_def inv_ShipT_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: PlaceableShip: (Grid * ShipT -> bool)
	PlaceableShip(g, s) ==
(((elems (s.Coords)) subset ALL_COORDINATES) and (forall ships in set (elems g) & (((elems (s.Coords)) inter (elems (ships.Coords))) = {})))\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 19:1\<close>

\<comment>\<open>VDM source: pre_PlaceableShip: (Grid * ShipT +> bool)
	pre_PlaceableShip(g, s) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 19:1\<close>
definition
	pre_PlaceableShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> bool"
where
	"pre_PlaceableShip g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_PlaceableShip` specification.\<close>
		((inv_Grid g)  \<and>  (inv_ShipT s))"


\<comment>\<open>VDM source: post_PlaceableShip: (Grid * ShipT * bool +> bool)
	post_PlaceableShip(g, s, RESULT) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 19:1\<close>
definition
	post_PlaceableShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_PlaceableShip g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_PlaceableShip` specification.\<close>
		(pre_PlaceableShip g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_ShipT s)  \<and>  (inv_bool RESULT)))"

definition
	PlaceableShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> bool"
where
	"PlaceableShip g   s \<equiv> 
	\<comment>\<open>User defined body of PlaceableShip.\<close>
	(((elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)) \<subseteq> GLOBAL.ALL_COORDINATES) \<and> (\<forall> ships \<in> (elems g)  . (((elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s)) \<inter> (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p ships))) = {})))"

	
	
\<comment>\<open>VDM source: PlaceShip: (Grid * ShipT -> Grid)
	PlaceShip(g, s) ==
(g ^ [s])
	pre PlaceableShip(g, s)
	post ((len RESULT) > (len g))\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 23:1\<close>

\<comment>\<open>VDM source: pre_PlaceShip: (Grid * ShipT +> bool)
	pre_PlaceShip(g, s) ==
PlaceableShip(g, s)\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 25:5\<close>
definition
	pre_PlaceShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> bool"
where
	"pre_PlaceShip g   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_PlaceShip` specification.\<close>
		((inv_Grid g)  \<and>  (inv_ShipT s))  \<and> 
		\<comment>\<open>User defined body of pre_PlaceShip.\<close>
		(PlaceableShip g  s)"


\<comment>\<open>VDM source: post_PlaceShip: (Grid * ShipT * Grid +> bool)
	post_PlaceShip(g, s, RESULT) ==
((len RESULT) > (len g))\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 26:17\<close>
definition
	post_PlaceShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> Grid \<Rightarrow> bool"
where
	"post_PlaceShip g   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_PlaceShip` specification.\<close>
		(pre_PlaceShip g  s \<longrightarrow> ((inv_Grid g)  \<and>  (inv_ShipT s)  \<and>  (inv_Grid RESULT)))  \<and> 
		\<comment>\<open>User defined body of post_PlaceShip.\<close>
		((len RESULT) > (len g))"

definition
	PlaceShip :: "Grid \<Rightarrow> ShipT \<Rightarrow> Grid"
where
	"PlaceShip g   s \<equiv> 
	\<comment>\<open>User defined body of PlaceShip.\<close>
	(g @ [s])"

	
	
\<comment>\<open>VDM source: Hit: (Grid * Coordinates -> (Grid * GuessResult))
	Hit(g, c) ==
(if (exists [s in set (elems g)] & (c in set (elems (s.Coords))))
then let i in set (inds g) be st (c in set (elems ((SeqGet)[ShipT](g, i).Coords))) in let hs:(Ship * GuessResult) = HitShip((SeqGet)[ShipT](g, i), c) in mk_((SeqReplaceAt)[ShipT](g, (hs.#1), i), (hs.#2))
else mk_(g, mk_GLOBAL`GuessResult(false, false)))\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 28:1\<close>

\<comment>\<open>VDM source: pre_Hit: (Grid * Coordinates +> bool)
	pre_Hit(g, c) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 28:1\<close>
definition
	pre_Hit :: "Grid \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"pre_Hit g   c \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Hit` specification.\<close>
		((inv_Grid g)  \<and>  inv_Coordinates c)"


\<comment>\<open>VDM source: post_Hit: (Grid * Coordinates * (Grid * GuessResult) +> bool)
	post_Hit(g, c, RESULT) ==
null\<close>
\<comment>\<open>in 'Grid' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Grid.vdmsl) at line 28:1\<close>
definition
	post_Hit :: "Grid \<Rightarrow> Coordinates \<Rightarrow> (Grid \<times> GuessResult) \<Rightarrow> bool"
where
	"post_Hit g   c   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Hit` specification.\<close>
		(pre_Hit g  c \<longrightarrow> ((inv_Grid g)  \<and>  inv_Coordinates c  \<and>  
		((inv_Grid (fst RESULT))\<and>
		 inv_GuessResult (snd RESULT)
		)))"

definition
	Hit :: "Grid \<Rightarrow> Coordinates \<Rightarrow> (Grid \<times> GuessResult)"
where
	"Hit g   c \<equiv> 
	\<comment>\<open>User defined body of Hit.\<close>
	(
		if ((\<exists> s \<in> (elems g)  . (c \<in> (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p s))))) then
		((
		SOME (dummy0::(ShipT VDMSeq \<times> GuessResult)) .(dummy0 \<in> { (
		let 
(hs::(Ship \<times> GuessResult)) = (Ship.HitShip (GLOBAL.SeqGet inv_Ship  g  i)  c)
		in
			
			(if (
		( (((inv_VDMSeq1' inv_Coordinates  (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p (fst hs)))) \<and> 
		 ((inv_VDMSeq1' (inv_bool) (Hit\<^sub>S\<^sub>h\<^sub>i\<^sub>p (fst hs)))) \<and> 
		 ((inv_VDMNat (Length\<^sub>S\<^sub>h\<^sub>i\<^sub>p (fst hs)))) )\<and>
		  (((inv_bool (Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd hs)))) \<and> 
		 ((inv_bool (Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd hs)))) )
		)) then
			((GLOBAL.SeqReplaceAt inv_Ship  g  (fst (hs))  i) , (snd (hs)))
		 else
			undefined
		)
		) | i .  ((i \<in>(inds g)))  \<and> (c \<in> (elems (Coords\<^sub>S\<^sub>h\<^sub>i\<^sub>p (GLOBAL.SeqGet inv_Ship  g  i)))) })))
		else
		((g , \<lparr>Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (False::\<bool>), Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (False::\<bool>)\<rparr>)))"



end