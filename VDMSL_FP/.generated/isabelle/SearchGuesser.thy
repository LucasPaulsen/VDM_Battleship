(* VDM to Isabelle Translation @2022-11-14T10:32:19.113Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl]
*)
theory SearchGuesser
imports "GLOBAL" "VDMToolkit" 
begin


\<comment>\<open>VDM source: NeighborCoords: (Coordinates -> set of (Coordinates))
	NeighborCoords(c) ==
((({mk_GLOBAL`Coordinates((c.X), ((c.Y) - 1))} union {mk_GLOBAL`Coordinates(((c.X) + 1), (c.Y))}) union {mk_GLOBAL`Coordinates((c.X), ((c.Y) + 1))}) union {mk_GLOBAL`Coordinates(((c.X) - 1), (c.Y))})\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 7:1\<close>

\<comment>\<open>VDM source: pre_NeighborCoords: (Coordinates +> bool)
	pre_NeighborCoords(c) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 7:1\<close>
definition
	pre_NeighborCoords :: "Coordinates \<Rightarrow> bool"
where
	"pre_NeighborCoords c \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_NeighborCoords` specification.\<close>
		(inv_Coordinates c)"


\<comment>\<open>VDM source: post_NeighborCoords: (Coordinates * set of (Coordinates) +> bool)
	post_NeighborCoords(c, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 7:1\<close>
definition
	post_NeighborCoords :: "Coordinates \<Rightarrow> Coordinates VDMSet \<Rightarrow> bool"
where
	"post_NeighborCoords c   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_NeighborCoords` specification.\<close>
		(pre_NeighborCoords c \<longrightarrow> (inv_Coordinates c  \<and>  (inv_VDMSet' inv_Coordinates  RESULT)))"

definition
	NeighborCoords :: "Coordinates \<Rightarrow> Coordinates VDMSet"
where
	"NeighborCoords c \<equiv> 
	\<comment>\<open>User defined body of NeighborCoords.\<close>
	((({\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) - (1::VDMNat1))\<rparr>} \<union> {\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr>}) \<union> {\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + (1::VDMNat1))\<rparr>}) \<union> {\<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) - (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr>})"

	
	
\<comment>\<open>VDM source: CommonNeighbors: (Coordinates * Coordinates -> set of (Coordinates))
	CommonNeighbors(c1, c2) ==
(NeighborCoords(c1) union NeighborCoords(c2))\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 15:1\<close>

\<comment>\<open>VDM source: pre_CommonNeighbors: (Coordinates * Coordinates +> bool)
	pre_CommonNeighbors(c1, c2) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 15:1\<close>
definition
	pre_CommonNeighbors :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"pre_CommonNeighbors c1   c2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_CommonNeighbors` specification.\<close>
		(inv_Coordinates c1  \<and>  inv_Coordinates c2)"


\<comment>\<open>VDM source: post_CommonNeighbors: (Coordinates * Coordinates * set of (Coordinates) +> bool)
	post_CommonNeighbors(c1, c2, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 15:1\<close>
definition
	post_CommonNeighbors :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> Coordinates VDMSet \<Rightarrow> bool"
where
	"post_CommonNeighbors c1   c2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_CommonNeighbors` specification.\<close>
		(pre_CommonNeighbors c1  c2 \<longrightarrow> (inv_Coordinates c1  \<and>  inv_Coordinates c2  \<and>  (inv_VDMSet' inv_Coordinates  RESULT)))"

definition
	CommonNeighbors :: "Coordinates \<Rightarrow> Coordinates \<Rightarrow> Coordinates VDMSet"
where
	"CommonNeighbors c1   c2 \<equiv> 
	\<comment>\<open>User defined body of CommonNeighbors.\<close>
	((NeighborCoords c1) \<union> (NeighborCoords c2))"

	
	
\<comment>\<open>VDM source: AreNeighbors: (set of (Coordinates) -> bool)
	AreNeighbors(sc) ==
(forall c1, c2 in set sc & ((((c1.X) = (c2.X)) and (((c1.Y) < (c2.Y)) => ({(c1.Y), ... ,(c2.Y)} subset Ycoords(sc)))) or (((c1.Y) = (c2.Y)) and (((c1.X) < (c2.X)) => ({(c1.X), ... ,(c2.X)} subset Xcoords(sc))))))\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 18:1\<close>

\<comment>\<open>VDM source: pre_AreNeighbors: (set of (Coordinates) +> bool)
	pre_AreNeighbors(sc) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 18:1\<close>
definition
	pre_AreNeighbors :: "Coordinates VDMSet \<Rightarrow> bool"
where
	"pre_AreNeighbors sc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_AreNeighbors` specification.\<close>
		((inv_VDMSet' inv_Coordinates  sc))"


\<comment>\<open>VDM source: post_AreNeighbors: (set of (Coordinates) * bool +> bool)
	post_AreNeighbors(sc, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 18:1\<close>
definition
	post_AreNeighbors :: "Coordinates VDMSet \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_AreNeighbors sc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_AreNeighbors` specification.\<close>
		(pre_AreNeighbors sc \<longrightarrow> ((inv_VDMSet' inv_Coordinates  sc)  \<and>  (inv_bool RESULT)))"

definition
	AreNeighbors :: "Coordinates VDMSet \<Rightarrow> bool"
where
	"AreNeighbors sc \<equiv> 
	\<comment>\<open>User defined body of AreNeighbors.\<close>
	(\<forall> c1 \<in> sc  . (\<forall> c2 \<in> sc  . ((((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<and> (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) < (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<longrightarrow> ({(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1)..(Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)} \<subseteq> (GLOBAL.Ycoords sc)))) \<or> (((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<and> (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) < (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)) \<longrightarrow> ({(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1)..(X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2)} \<subseteq> (GLOBAL.Xcoords sc)))))))"

	
	
\<comment>\<open>VDM source: NextNeighbors: (set of (Coordinates) -> set of (Coordinates))
	NextNeighbors(sc) ==
let c1, c2 in set sc be st (c1 <> c2) in (if ((c1.X) = (c2.X))
then (({mk_GLOBAL`Coordinates((c.X), ((c.Y) - 1)) | c in set sc} union {mk_GLOBAL`Coordinates((c.X), ((c.Y) + 1)) | c in set sc}) \ sc)
else (({mk_GLOBAL`Coordinates(((c.X) - 1), (c.Y)) | c in set sc} union {mk_GLOBAL`Coordinates(((c.X) + 1), (c.Y)) | c in set sc}) \ sc))
	pre AreNeighbors(sc)\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 23:1\<close>

\<comment>\<open>VDM source: pre_NextNeighbors: (set of (Coordinates) +> bool)
	pre_NextNeighbors(sc) ==
AreNeighbors(sc)\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 30:5\<close>
definition
	pre_NextNeighbors :: "Coordinates VDMSet \<Rightarrow> bool"
where
	"pre_NextNeighbors sc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_NextNeighbors` specification.\<close>
		((inv_VDMSet' inv_Coordinates  sc))  \<and> 
		\<comment>\<open>User defined body of pre_NextNeighbors.\<close>
		(AreNeighbors sc)"


\<comment>\<open>VDM source: post_NextNeighbors: (set of (Coordinates) * set of (Coordinates) +> bool)
	post_NextNeighbors(sc, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 23:1\<close>
definition
	post_NextNeighbors :: "Coordinates VDMSet \<Rightarrow> Coordinates VDMSet \<Rightarrow> bool"
where
	"post_NextNeighbors sc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_NextNeighbors` specification.\<close>
		(pre_NextNeighbors sc \<longrightarrow> ((inv_VDMSet' inv_Coordinates  sc)  \<and>  (inv_VDMSet' inv_Coordinates  RESULT)))"

definition
	NextNeighbors :: "Coordinates VDMSet \<Rightarrow> Coordinates VDMSet"
where
	"NextNeighbors sc \<equiv> 
	\<comment>\<open>User defined body of NextNeighbors.\<close>
	(
		SOME (dummy0::Coordinates VDMSet) .(dummy0 \<in> { (
		if (((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c1) = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c2))) then
		((({ \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) - (1::VDMNat1))\<rparr> | c .  ((c \<in>sc))  } \<union> { \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + (1::VDMNat1))\<rparr> | c .  ((c \<in>sc))  }) - sc))
		else
		((({ \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) - (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr> | c .  ((c \<in>sc))  } \<union> { \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = ((X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) + (1::VDMNat1)), Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c)\<rparr> | c .  ((c \<in>sc))  }) - sc))) | c1   c2 .  ((c1 \<in>sc)) \<and>  ((c2 \<in>sc))  \<and> (c1 \<noteq> c2) }))"

	
	
\<comment>\<open>VDM source: RecentHit: (seq of (GuessResult) * seq of (Coordinates) -> seq of (Coordinates))
	RecentHit(gr, c) ==
(if (gr = [])
then []
else (if ((hd gr).Hit)
then [(hd c)]
else RecentHit((tl gr), (tl c))))
	measure (card (inds gr))\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 32:1\<close>

\<comment>\<open>VDM source: pre_RecentHit: (seq of (GuessResult) * seq of (Coordinates) +> bool)
	pre_RecentHit(gr, c) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 32:1\<close>
definition
	pre_RecentHit :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> bool"
where
	"pre_RecentHit gr   c \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_RecentHit` specification.\<close>
		((inv_VDMSeq' inv_GuessResult  gr)  \<and>  (inv_VDMSeq' inv_Coordinates  c))"


\<comment>\<open>VDM source: post_RecentHit: (seq of (GuessResult) * seq of (Coordinates) * seq of (Coordinates) +> bool)
	post_RecentHit(gr, c, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 32:1\<close>
definition
	post_RecentHit :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> bool"
where
	"post_RecentHit gr   c   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_RecentHit` specification.\<close>
		(pre_RecentHit gr  c \<longrightarrow> ((inv_VDMSeq' inv_GuessResult  gr)  \<and>  (inv_VDMSeq' inv_Coordinates  c)  \<and>  (inv_VDMSeq' inv_Coordinates  RESULT)))"

fun
	RecentHit :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq"
where
	"RecentHit gr   c = 
	\<comment>\<open>User defined body of RecentHit.\<close>
	(
		if ((gr = [])) then
		([])
		else
		((
		if ((Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (hd gr))) then
		([(hd c)])
		else
		((RecentHit (tl gr)  (tl c))))))"

	
	
\<comment>\<open>VDM source: Recent2Hits: (seq of (GuessResult) * seq of (Coordinates) * seq of (Coordinates) -> seq of (Coordinates))
	Recent2Hits(gr, c, acc) ==
(if (gr = [])
then acc
else (if ((len acc) = 2)
then acc
else (if ((hd gr).Hit)
then Recent2Hits((tl gr), (tl c), (acc ^ [(hd c)]))
else Recent2Hits((tl gr), (tl c), acc))))
	measure (card (inds gr))\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 38:1\<close>

\<comment>\<open>VDM source: pre_Recent2Hits: (seq of (GuessResult) * seq of (Coordinates) * seq of (Coordinates) +> bool)
	pre_Recent2Hits(gr, c, acc) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 38:1\<close>
definition
	pre_Recent2Hits :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> bool"
where
	"pre_Recent2Hits gr   c   acc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Recent2Hits` specification.\<close>
		((inv_VDMSeq' inv_GuessResult  gr)  \<and>  (inv_VDMSeq' inv_Coordinates  c)  \<and>  (inv_VDMSeq' inv_Coordinates  acc))"


\<comment>\<open>VDM source: post_Recent2Hits: (seq of (GuessResult) * seq of (Coordinates) * seq of (Coordinates) * seq of (Coordinates) +> bool)
	post_Recent2Hits(gr, c, acc, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 38:1\<close>
definition
	post_Recent2Hits :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> bool"
where
	"post_Recent2Hits gr   c   acc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Recent2Hits` specification.\<close>
		(pre_Recent2Hits gr  c  acc \<longrightarrow> ((inv_VDMSeq' inv_GuessResult  gr)  \<and>  (inv_VDMSeq' inv_Coordinates  c)  \<and>  (inv_VDMSeq' inv_Coordinates  acc)  \<and>  (inv_VDMSeq' inv_Coordinates  RESULT)))"

fun
	Recent2Hits :: "GuessResult VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq \<Rightarrow> Coordinates VDMSeq"
where
	"Recent2Hits gr   c   acc = 
	\<comment>\<open>User defined body of Recent2Hits.\<close>
	(
		if ((gr = [])) then
		(acc)
		else
		((
		if (((len acc) = (2::VDMNat1))) then
		(acc)
		else
		((
		if ((Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (hd gr))) then
		((Recent2Hits (tl gr)  (tl c)  (acc @ [(hd c)])))
		else
		((Recent2Hits (tl gr)  (tl c)  acc)))))))"

	
	
\<comment>\<open>VDM source: Unchecked: (set of (Coordinates) * set of (Coordinates) -> set of (Coordinates))
	Unchecked(in_sc, checked_sc) ==
{c | c in set in_sc & (c not in set checked_sc)}\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 48:1\<close>

\<comment>\<open>VDM source: pre_Unchecked: (set of (Coordinates) * set of (Coordinates) +> bool)
	pre_Unchecked(in_sc, checked_sc) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 48:1\<close>
definition
	pre_Unchecked :: "Coordinates VDMSet \<Rightarrow> Coordinates VDMSet \<Rightarrow> bool"
where
	"pre_Unchecked in_sc   checked_sc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Unchecked` specification.\<close>
		((inv_VDMSet' inv_Coordinates  in_sc)  \<and>  (inv_VDMSet' inv_Coordinates  checked_sc))"


\<comment>\<open>VDM source: post_Unchecked: (set of (Coordinates) * set of (Coordinates) * set of (Coordinates) +> bool)
	post_Unchecked(in_sc, checked_sc, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 48:1\<close>
definition
	post_Unchecked :: "Coordinates VDMSet \<Rightarrow> Coordinates VDMSet \<Rightarrow> Coordinates VDMSet \<Rightarrow> bool"
where
	"post_Unchecked in_sc   checked_sc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Unchecked` specification.\<close>
		(pre_Unchecked in_sc  checked_sc \<longrightarrow> ((inv_VDMSet' inv_Coordinates  in_sc)  \<and>  (inv_VDMSet' inv_Coordinates  checked_sc)  \<and>  (inv_VDMSet' inv_Coordinates  RESULT)))"

definition
	Unchecked :: "Coordinates VDMSet \<Rightarrow> Coordinates VDMSet \<Rightarrow> Coordinates VDMSet"
where
	"Unchecked in_sc   checked_sc \<equiv> 
	\<comment>\<open>User defined body of Unchecked.\<close>
	{ c .   ((c \<in>in_sc))  \<and> (c \<notin> checked_sc) }"

	
	
\<comment>\<open>VDM source: DefaultNextC: (GuessHistory -> Coordinates)
	DefaultNextC(gh) ==
let c in set (ALL_COORDINATES \ (elems (gh.Coords))) in c\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 55:1\<close>

\<comment>\<open>VDM source: pre_DefaultNextC: (GuessHistory +> bool)
	pre_DefaultNextC(gh) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 55:1\<close>
definition
	pre_DefaultNextC :: "GuessHistory \<Rightarrow> bool"
where
	"pre_DefaultNextC gh \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_DefaultNextC` specification.\<close>
		(inv_GuessHistory gh)"


\<comment>\<open>VDM source: post_DefaultNextC: (GuessHistory * Coordinates +> bool)
	post_DefaultNextC(gh, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 55:1\<close>
definition
	post_DefaultNextC :: "GuessHistory \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"post_DefaultNextC gh   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultNextC` specification.\<close>
		(pre_DefaultNextC gh \<longrightarrow> (inv_GuessHistory gh  \<and>  inv_Coordinates RESULT))"

definition
	DefaultNextC :: "GuessHistory \<Rightarrow> Coordinates"
where
	"DefaultNextC gh \<equiv> 
	\<comment>\<open>User defined body of DefaultNextC.\<close>
	(
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>(GLOBAL.ALL_COORDINATES - (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh)))))  }))"

	
	
\<comment>\<open>VDM source: SearchGuess: (GuessHistory -> Coordinates)
	SearchGuess(gh) ==
(if ((card (elems (gh.Coords))) < 1)
then let c in set ALL_COORDINATES in c
else let r2h:seq of (Coordinates) = Recent2Hits((gh.Results), (gh.Coords), []) in (if ((card (elems r2h)) = 2)
then (if AreNeighbors((elems r2h))
then let nextCoords:set of (Coordinates) = NextNeighbors((elems r2h)) in let unchecked:set of (Coordinates) = (Unchecked(nextCoords, (elems (gh.Coords))) inter ALL_COORDINATES) in (if (unchecked <> {})
then let c in set unchecked in c
else DefaultNextC(gh))
else let neighbors:set of (Coordinates) = NeighborCoords((hd r2h)) in let unchecked:set of (Coordinates) = (Unchecked(neighbors, (elems (gh.Coords))) inter ALL_COORDINATES) in (if (not (unchecked = {}))
then let c in set unchecked in c
else DefaultNextC(gh)))
else let rh:seq of (Coordinates) = RecentHit((gh.Results), (gh.Coords)) in (if ((card (elems rh)) = 1)
then let neighbors:set of (Coordinates) = NeighborCoords((hd rh)) in let unchecked:set of (Coordinates) = (Unchecked(neighbors, (elems (gh.Coords))) inter ALL_COORDINATES) in (if (not (unchecked = {}))
then let c in set unchecked in c
else DefaultNextC(gh))
else DefaultNextC(gh))))\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 58:1\<close>

\<comment>\<open>VDM source: pre_SearchGuess: (GuessHistory +> bool)
	pre_SearchGuess(gh) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 58:1\<close>
definition
	pre_SearchGuess :: "GuessHistory \<Rightarrow> bool"
where
	"pre_SearchGuess gh \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_SearchGuess` specification.\<close>
		(inv_GuessHistory gh)"


\<comment>\<open>VDM source: post_SearchGuess: (GuessHistory * Coordinates +> bool)
	post_SearchGuess(gh, RESULT) ==
null\<close>
\<comment>\<open>in 'SearchGuesser' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\SearchGuesser.vdmsl) at line 58:1\<close>
definition
	post_SearchGuess :: "GuessHistory \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"post_SearchGuess gh   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_SearchGuess` specification.\<close>
		(pre_SearchGuess gh \<longrightarrow> (inv_GuessHistory gh  \<and>  inv_Coordinates RESULT))"

definition
	SearchGuess :: "GuessHistory \<Rightarrow> Coordinates"
where
	"SearchGuess gh \<equiv> 
	\<comment>\<open>User defined body of SearchGuess.\<close>
	(
		if (((vdm_card (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))) < (1::VDMNat1))) then
		((
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>GLOBAL.ALL_COORDINATES))  })))
		else
		((
		let 
(r2h::Coordinates VDMSeq) = (Recent2Hits (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh)  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh)  [])
		in
			
			(if ((inv_VDMSeq' inv_Coordinates  r2h)) then
			(
		if (((vdm_card (elems r2h)) = (2::VDMNat1))) then
		((
		if ((AreNeighbors (elems r2h))) then
		((
		let 
(nextCoords::Coordinates VDMSet) = (NextNeighbors (elems r2h))
		in
			
			(if ((inv_VDMSet' inv_Coordinates  nextCoords)) then
			(
		let 
(unchecked::Coordinates VDMSet) = ((Unchecked nextCoords  (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))) \<inter> GLOBAL.ALL_COORDINATES)
		in
			
			(if ((inv_VDMSet' inv_Coordinates  unchecked)) then
			(
		if ((unchecked \<noteq> {})) then
		((
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>unchecked))  })))
		else
		((DefaultNextC gh)))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		))
		else
		((
		let 
(neighbors::Coordinates VDMSet) = (NeighborCoords (hd r2h))
		in
			
			(if ((inv_VDMSet' inv_Coordinates  neighbors)) then
			(
		let 
(unchecked::Coordinates VDMSet) = ((Unchecked neighbors  (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))) \<inter> GLOBAL.ALL_COORDINATES)
		in
			
			(if ((inv_VDMSet' inv_Coordinates  unchecked)) then
			(
		if ((\<not> (unchecked = {}))) then
		((
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>unchecked))  })))
		else
		((DefaultNextC gh)))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		))))
		else
		((
		let 
(rh::Coordinates VDMSeq) = (RecentHit (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh)  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))
		in
			
			(if ((inv_VDMSeq' inv_Coordinates  rh)) then
			(
		if (((vdm_card (elems rh)) = (1::VDMNat1))) then
		((
		let 
(neighbors::Coordinates VDMSet) = (NeighborCoords (hd rh))
		in
			
			(if ((inv_VDMSet' inv_Coordinates  neighbors)) then
			(
		let 
(unchecked::Coordinates VDMSet) = ((Unchecked neighbors  (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y gh))) \<inter> GLOBAL.ALL_COORDINATES)
		in
			
			(if ((inv_VDMSet' inv_Coordinates  unchecked)) then
			(
		if ((\<not> (unchecked = {}))) then
		((
		SOME (dummy0::Coordinates) .(dummy0 \<in> { c .   ((c \<in>unchecked))  })))
		else
		((DefaultNextC gh)))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		))
		else
		((DefaultNextC gh)))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		)))"



end