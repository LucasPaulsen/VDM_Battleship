(* VDM to Isabelle Translation @2022-11-14T10:32:19.085Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl]
*)
theory GLOBAL
imports "VDMToolkit" 
begin


\<comment>\<open>VDM source: Coordinates = compose Coordinates of X:nat, Y:nat end\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 6:1\<close>
record Coordinates =  X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s :: "VDMNat"
		 
		 Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s :: "VDMNat" 

\<comment>\<open>VDM source: inv_Coordinates: (Coordinates +> bool)
	inv_Coordinates(dummy0) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 6:1\<close>
definition
	inv_Coordinates :: "Coordinates \<Rightarrow> bool"
where
	"inv_Coordinates dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Coordinates` specification.\<close>
		( (((inv_VDMNat (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s dummy0))) \<and> 
		 ((inv_VDMNat (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s dummy0))) ))"
 
lemmas inv_Coordinates_defs = inv_Coordinates_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: GuessResult = compose GuessResult of Hit:bool, Sunk:bool end\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 10:1\<close>
record GuessResult =  Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "bool"
		 
		 Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "bool" 

\<comment>\<open>VDM source: inv_GuessResult: (GuessResult +> bool)
	inv_GuessResult(dummy0) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 10:1\<close>
definition
	inv_GuessResult :: "GuessResult \<Rightarrow> bool"
where
	"inv_GuessResult dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_GuessResult` specification.\<close>
		( (((inv_bool (Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_bool (Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) ))"
 
lemmas inv_GuessResult_defs = inv_GuessResult_def inv_bool_def 


	
	
\<comment>\<open>VDM source: GuessHistory = compose GuessHistory of Coords:seq of (Coordinates), Results:seq of (GuessResult) end\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 14:1\<close>
record GuessHistory =  Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y :: "Coordinates VDMSeq"
		 
		 Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y :: "GuessResult VDMSeq" 

\<comment>\<open>VDM source: inv_GuessHistory: (GuessHistory +> bool)
	inv_GuessHistory(dummy0) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 14:1\<close>
definition
	inv_GuessHistory :: "GuessHistory \<Rightarrow> bool"
where
	"inv_GuessHistory dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_GuessHistory` specification.\<close>
		( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y dummy0))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y dummy0))) ))"
 
lemmas inv_GuessHistory_defs = inv_Coordinates_def inv_GuessHistory_def inv_GuessResult_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: N_ROWS:nat = 5\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 19:1\<close>
abbreviation
	N_ROWS :: "VDMNat"
where
	"N_ROWS \<equiv> (5::VDMNat1)"

	definition
	inv_N_ROWS :: "\<bool>"
where
	"inv_N_ROWS  \<equiv> (inv_VDMNat N_ROWS)"

	
	
	
\<comment>\<open>VDM source: N_COLS:nat = 5\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 20:1\<close>
abbreviation
	N_COLS :: "VDMNat"
where
	"N_COLS \<equiv> (5::VDMNat1)"

	definition
	inv_N_COLS :: "\<bool>"
where
	"inv_N_COLS  \<equiv> (inv_VDMNat N_COLS)"

	
	
	
\<comment>\<open>VDM source: MIN_LEN:nat = 2\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 21:1\<close>
abbreviation
	MIN_LEN :: "VDMNat"
where
	"MIN_LEN \<equiv> (2::VDMNat1)"

	definition
	inv_MIN_LEN :: "\<bool>"
where
	"inv_MIN_LEN  \<equiv> (inv_VDMNat MIN_LEN)"

	
	
	
\<comment>\<open>VDM source: MAX_LEN:nat = 4\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 22:1\<close>
abbreviation
	MAX_LEN :: "VDMNat"
where
	"MAX_LEN \<equiv> (4::VDMNat1)"

	definition
	inv_MAX_LEN :: "\<bool>"
where
	"inv_MAX_LEN  \<equiv> (inv_VDMNat MAX_LEN)"

	
	
	
\<comment>\<open>VDM source: SHIPS_BY_LEN:seq of (nat) = [2, 2, 3, 4]\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 23:1\<close>
abbreviation
	SHIPS_BY_LEN :: "VDMNat VDMSeq"
where
	"SHIPS_BY_LEN \<equiv> [(2::VDMNat1) , (2::VDMNat1) , (3::VDMNat1) , (4::VDMNat1)]"

	definition
	inv_SHIPS_BY_LEN :: "\<bool>"
where
	"inv_SHIPS_BY_LEN  \<equiv> (inv_VDMSeq' (inv_VDMNat) SHIPS_BY_LEN)"

	
	
	
\<comment>\<open>VDM source: N_SHIPS:nat = (len SHIPS_BY_LEN)\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 24:1\<close>
abbreviation
	N_SHIPS :: "VDMNat"
where
	"N_SHIPS \<equiv> (len SHIPS_BY_LEN)"

	definition
	inv_N_SHIPS :: "\<bool>"
where
	"inv_N_SHIPS  \<equiv> (inv_VDMNat N_SHIPS)"

	
	
	
\<comment>\<open>VDM source: ALL_COORDINATES:set of (Coordinates) = {mk_Coordinates(x, y) | x in set {1, ... ,N_COLS}, y in set {1, ... ,N_ROWS}}\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 25:1\<close>
abbreviation
	ALL_COORDINATES :: "Coordinates VDMSet"
where
	"ALL_COORDINATES \<equiv> { \<lparr>X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = x, Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s = y\<rparr> | x  y .  ((x \<in>{(1::VDMNat1)..N_COLS}))  \<and>  ((y \<in>{(1::VDMNat1)..N_ROWS}))  }"

	definition
	inv_ALL_COORDINATES :: "\<bool>"
where
	"inv_ALL_COORDINATES  \<equiv> (inv_VDMSet' inv_Coordinates  ALL_COORDINATES)"

	
	
	
\<comment>\<open>VDM source: MAX_TOTAL_GUESSES:nat = ((card ALL_COORDINATES) + (card ALL_COORDINATES))\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 27:1\<close>
abbreviation
	MAX_TOTAL_GUESSES :: "VDMNat"
where
	"MAX_TOTAL_GUESSES \<equiv> ((vdm_card ALL_COORDINATES) + (vdm_card ALL_COORDINATES))"

	definition
	inv_MAX_TOTAL_GUESSES :: "\<bool>"
where
	"inv_MAX_TOTAL_GUESSES  \<equiv> (inv_VDMNat MAX_TOTAL_GUESSES)"

	
	
	
\<comment>\<open>VDM source: Xcoords: (set of (Coordinates) -> set of (nat))
	Xcoords(coordSet) ==
{(c.X) | c in set coordSet}\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 31:1\<close>

\<comment>\<open>VDM source: pre_Xcoords: (set of (Coordinates) +> bool)
	pre_Xcoords(coordSet) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 31:1\<close>
definition
	pre_Xcoords :: "Coordinates VDMSet \<Rightarrow> bool"
where
	"pre_Xcoords coordSet \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Xcoords` specification.\<close>
		((inv_VDMSet' inv_Coordinates  coordSet))"


\<comment>\<open>VDM source: post_Xcoords: (set of (Coordinates) * set of (nat) +> bool)
	post_Xcoords(coordSet, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 31:1\<close>
definition
	post_Xcoords :: "Coordinates VDMSet \<Rightarrow> VDMNat VDMSet \<Rightarrow> bool"
where
	"post_Xcoords coordSet   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Xcoords` specification.\<close>
		(pre_Xcoords coordSet \<longrightarrow> ((inv_VDMSet' inv_Coordinates  coordSet)  \<and>  (inv_VDMSet' (inv_VDMNat) RESULT)))"

definition
	Xcoords :: "Coordinates VDMSet \<Rightarrow> VDMNat VDMSet"
where
	"Xcoords coordSet \<equiv> 
	\<comment>\<open>User defined body of Xcoords.\<close>
	{ (X\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) | c .  ((c \<in>coordSet))  }"

	
	
\<comment>\<open>VDM source: Ycoords: (set of (Coordinates) -> set of (nat))
	Ycoords(coordSet) ==
{(c.Y) | c in set coordSet}\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 34:1\<close>

\<comment>\<open>VDM source: pre_Ycoords: (set of (Coordinates) +> bool)
	pre_Ycoords(coordSet) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 34:1\<close>
definition
	pre_Ycoords :: "Coordinates VDMSet \<Rightarrow> bool"
where
	"pre_Ycoords coordSet \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Ycoords` specification.\<close>
		((inv_VDMSet' inv_Coordinates  coordSet))"


\<comment>\<open>VDM source: post_Ycoords: (set of (Coordinates) * set of (nat) +> bool)
	post_Ycoords(coordSet, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 34:1\<close>
definition
	post_Ycoords :: "Coordinates VDMSet \<Rightarrow> VDMNat VDMSet \<Rightarrow> bool"
where
	"post_Ycoords coordSet   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Ycoords` specification.\<close>
		(pre_Ycoords coordSet \<longrightarrow> ((inv_VDMSet' inv_Coordinates  coordSet)  \<and>  (inv_VDMSet' (inv_VDMNat) RESULT)))"

definition
	Ycoords :: "Coordinates VDMSet \<Rightarrow> VDMNat VDMSet"
where
	"Ycoords coordSet \<equiv> 
	\<comment>\<open>User defined body of Ycoords.\<close>
	{ (Y\<^sub>C\<^sub>o\<^sub>o\<^sub>r\<^sub>d\<^sub>i\<^sub>n\<^sub>a\<^sub>t\<^sub>e\<^sub>s c) | c .  ((c \<in>coordSet))  }"

	
	
\<comment>\<open>VDM source: SeqGet[T]: (seq of (@T) * nat1 -> @T)
	SeqGet(s, i) ==
s(i)\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 37:1\<close>

\<comment>\<open>VDM source: pre_SeqGet[T]: (seq of (@T) * nat1 +> bool)
	pre_SeqGet(s, i) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 37:1\<close>
definition
	pre_SeqGet :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> VDMNat1 \<Rightarrow> bool"
where
	"pre_SeqGet inv_T   s   i \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_SeqGet` specification.\<close>
		((inv_VDMSeq' inv_T s)  \<and>  (inv_VDMNat1 i))"


\<comment>\<open>VDM source: post_SeqGet[T]: (seq of (@T) * nat1 * @T +> bool)
	post_SeqGet(s, i, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 37:1\<close>
definition
	post_SeqGet :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> VDMNat1 \<Rightarrow> 'T \<Rightarrow> bool"
where
	"post_SeqGet inv_T   s   i   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_SeqGet` specification.\<close>
		(pre_SeqGet inv_T  s  i \<longrightarrow> ((inv_VDMSeq' inv_T s)  \<and>  (inv_VDMNat1 i)  \<and>  inv_T RESULT))"

definition
	SeqGet :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> VDMNat1 \<Rightarrow> 'T"
where
	"SeqGet inv_T   s   i \<equiv> 
	\<comment>\<open>User defined body of SeqGet.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `SeqGet`.\<close>
	(if post_SeqGet inv_T   s   i ((s$i)) then	(s$i) else	undefined)"

	
	
\<comment>\<open>VDM source: SeqReplaceAt[T]: (seq of (@T) * @T * nat1 -> seq of (@T))
	SeqReplaceAt(s, e, i) ==
let s1:seq of (@T) = [s(x) | x in set (inds s) & (x < i)], s2:seq of (@T) = [s(x) | x in set (inds s) & (x > i)] in ((s1 ^ [e]) ^ s2)\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 40:1\<close>

\<comment>\<open>VDM source: pre_SeqReplaceAt[T]: (seq of (@T) * @T * nat1 +> bool)
	pre_SeqReplaceAt(s, e, i) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 40:1\<close>
definition
	pre_SeqReplaceAt :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> VDMNat1 \<Rightarrow> bool"
where
	"pre_SeqReplaceAt inv_T   s   e   i \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_SeqReplaceAt` specification.\<close>
		((inv_VDMSeq' inv_T s)  \<and>  inv_T e  \<and>  (inv_VDMNat1 i))"


\<comment>\<open>VDM source: post_SeqReplaceAt[T]: (seq of (@T) * @T * nat1 * seq of (@T) +> bool)
	post_SeqReplaceAt(s, e, i, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 40:1\<close>
definition
	post_SeqReplaceAt :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> VDMNat1 \<Rightarrow> 'T VDMSeq \<Rightarrow> bool"
where
	"post_SeqReplaceAt inv_T   s   e   i   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_SeqReplaceAt` specification.\<close>
		(pre_SeqReplaceAt inv_T  s  e  i \<longrightarrow> ((inv_VDMSeq' inv_T s)  \<and>  inv_T e  \<and>  (inv_VDMNat1 i)  \<and>  (inv_VDMSeq' inv_T RESULT)))"

definition
	SeqReplaceAt :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> VDMNat1 \<Rightarrow> 'T VDMSeq"
where
	"SeqReplaceAt inv_T   s   e   i \<equiv> 
	\<comment>\<open>User defined body of SeqReplaceAt.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `SeqReplaceAt`.\<close>
	(if post_SeqReplaceAt inv_T   s   e   i ((
		let 
(s1::'T VDMSeq) = [ (s$x) . x \<leftarrow> sorted_list_of_set ((inds s)) , ((x \<in>(inds s))) , (x < i) ]
		;
		
(s2::'T VDMSeq) = [ (s$x) . x \<leftarrow> sorted_list_of_set ((inds s)) , ((x \<in>(inds s))) , (x > i) ]
		in
			
			(if ((inv_VDMSeq' inv_T s1))
	 \<and> 
	((inv_VDMSeq' inv_T s2)) then
			((s1 @ [e]) @ s2)
		 else
			undefined
		)
		)) then
			(
		let 
(s1::'T VDMSeq) = [ (s$x) . x \<leftarrow> sorted_list_of_set ((inds s)) , ((x \<in>(inds s))) , (x < i) ]
		;
		
(s2::'T VDMSeq) = [ (s$x) . x \<leftarrow> sorted_list_of_set ((inds s)) , ((x \<in>(inds s))) , (x > i) ]
		in
			
			(if ((inv_VDMSeq' inv_T s1))
	 \<and> 
	((inv_VDMSeq' inv_T s2)) then
			((s1 @ [e]) @ s2)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		"

	
	
\<comment>\<open>VDM source: SeqNOccurs[T]: (seq of (@T) * @T -> nat)
	SeqNOccurs(s, e) ==
(if (s = [])
then 0
else (if ((hd s) = e)
then (1 + (SeqNOccurs)[@T]((tl s), e))
else (SeqNOccurs)[@T]((tl s), e)))\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 45:1\<close>

\<comment>\<open>VDM source: pre_SeqNOccurs[T]: (seq of (@T) * @T +> bool)
	pre_SeqNOccurs(s, e) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 45:1\<close>
definition
	pre_SeqNOccurs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> bool"
where
	"pre_SeqNOccurs inv_T   s   e \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_SeqNOccurs` specification.\<close>
		((inv_VDMSeq' inv_T s)  \<and>  inv_T e)"


\<comment>\<open>VDM source: post_SeqNOccurs[T]: (seq of (@T) * @T * nat +> bool)
	post_SeqNOccurs(s, e, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 45:1\<close>
definition
	post_SeqNOccurs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_SeqNOccurs inv_T   s   e   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_SeqNOccurs` specification.\<close>
		(pre_SeqNOccurs inv_T  s  e \<longrightarrow> ((inv_VDMSeq' inv_T s)  \<and>  inv_T e  \<and>  (inv_VDMNat RESULT)))"

fun
	SeqNOccurs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> VDMNat"
where
	"SeqNOccurs inv_T   s   e = 
	\<comment>\<open>User defined body of SeqNOccurs.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `SeqNOccurs`.\<close>
	(if post_SeqNOccurs inv_T   s   e ((
		if ((s = [])) then
		((0::VDMNat))
		else
		((
		if (((hd s) = e)) then
		(((1::VDMNat1) + (SeqNOccurs inv_T  (tl s)  e)))
		else
		((SeqNOccurs inv_T  (tl s)  e)))))) then
			(
		if ((s = [])) then
		((0::VDMNat))
		else
		((
		if (((hd s) = e)) then
		(((1::VDMNat1) + (SeqNOccurs inv_T  (tl s)  e)))
		else
		((SeqNOccurs inv_T  (tl s)  e)))))
		 else
			undefined
		)
		"

	
	
\<comment>\<open>VDM source: SimilarSeqs[T]: (seq of (@T) * seq of (@T) -> bool)
	SimilarSeqs(s1, s2) ==
(((len s1) = (len s2)) and (forall e in set (elems s1) & ((SeqNOccurs)[@T](s1, e) = (SeqNOccurs)[@T](s2, e))))\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 50:1\<close>

\<comment>\<open>VDM source: pre_SimilarSeqs[T]: (seq of (@T) * seq of (@T) +> bool)
	pre_SimilarSeqs(s1, s2) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 50:1\<close>
definition
	pre_SimilarSeqs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T VDMSeq \<Rightarrow> bool"
where
	"pre_SimilarSeqs inv_T   s1   s2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_SimilarSeqs` specification.\<close>
		((inv_VDMSeq' inv_T s1)  \<and>  (inv_VDMSeq' inv_T s2))"


\<comment>\<open>VDM source: post_SimilarSeqs[T]: (seq of (@T) * seq of (@T) * bool +> bool)
	post_SimilarSeqs(s1, s2, RESULT) ==
null\<close>
\<comment>\<open>in 'GLOBAL' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GLOBAL.vdmsl) at line 50:1\<close>
definition
	post_SimilarSeqs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T VDMSeq \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_SimilarSeqs inv_T   s1   s2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_SimilarSeqs` specification.\<close>
		(pre_SimilarSeqs inv_T  s1  s2 \<longrightarrow> ((inv_VDMSeq' inv_T s1)  \<and>  (inv_VDMSeq' inv_T s2)  \<and>  (inv_bool RESULT)))"

definition
	SimilarSeqs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T VDMSeq \<Rightarrow> bool"
where
	"SimilarSeqs inv_T   s1   s2 \<equiv> 
	\<comment>\<open>User defined body of SimilarSeqs.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `SimilarSeqs`.\<close>
	(if post_SimilarSeqs inv_T   s1   s2 ((((len s1) = (len s2)) \<and> (\<forall> e \<in> (elems s1)  . ((SeqNOccurs inv_T  s1  e) = (SeqNOccurs inv_T  s2  e))))) then	(((len s1) = (len s2)) \<and> (\<forall> e \<in> (elems s1)  . ((SeqNOccurs inv_T  s1  e) = (SeqNOccurs inv_T  s2  e)))) else	undefined)"



end