(* VDM to Isabelle Translation @2022-11-14T10:32:19.078Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl]
*)
theory GameController
imports "GLOBAL" "Player" "VDMToolkit" 
begin


\<comment>\<open>VDM source: NAT_STR:seq1 of (seq1 of (char)) = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 8:5\<close>
abbreviation
	NAT_STR :: "VDMChar VDMSeq1 VDMSeq1"
where
	"NAT_STR \<equiv> [(''0'') , (''1'') , (''2'') , (''3'') , (''4'') , (''5'') , (''6'') , (''7'') , (''8'') , (''9'')]"

	definition
	inv_NAT_STR :: "\<bool>"
where
	"inv_NAT_STR  \<equiv> (inv_VDMSeq1' (inv_VDMSeq1' (inv_VDMChar)) NAT_STR)"

	
	
	
\<comment>\<open>VDM source: GameController = compose GameController of Attacker:Player, Defender:Player end
	inv g == ((g.Attacker) <> (g.Defender))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 11:1\<close>
record GameController =  Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r :: "Player"
		 
		 Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r :: "Player" 

\<comment>\<open>VDM source: inv_GameController: (GameController +> bool)
	inv_GameController(g) ==
((g.Attacker) <> (g.Defender))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 14:25\<close>
definition
	inv_GameController :: "GameController \<Rightarrow> bool"
where
	"inv_GameController g \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_GameController` specification.\<close>
		( ((inv_Player (Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g)) \<and> 
		 (inv_Player (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g)) ))  \<and> 
		\<comment>\<open>User defined body of inv_GameController.\<close>
		((Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g) \<noteq> (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g))"
 
lemmas inv_GameController_defs = inv_ArngType_def inv_Coordinates_def inv_GameController_def inv_Grid_def inv_GuesType_def inv_GuessHistory_def inv_GuessResult_def inv_Player_def inv_Ship_def inv_ShipT_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: MakeGameController: (Player * Player -> GameController)
	MakeGameController(p1, p2) ==
mk_GameController(p1, p2)\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 17:1\<close>

\<comment>\<open>VDM source: pre_MakeGameController: (Player * Player +> bool)
	pre_MakeGameController(p1, p2) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 17:1\<close>
definition
	pre_MakeGameController :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_MakeGameController p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_MakeGameController` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_MakeGameController: (Player * Player * GameController +> bool)
	post_MakeGameController(p1, p2, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 17:1\<close>
definition
	post_MakeGameController :: "Player \<Rightarrow> Player \<Rightarrow> GameController \<Rightarrow> bool"
where
	"post_MakeGameController p1   p2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_MakeGameController` specification.\<close>
		(pre_MakeGameController p1  p2 \<longrightarrow> (inv_Player p1  \<and>  inv_Player p2  \<and>  inv_GameController RESULT))"

definition
	MakeGameController :: "Player \<Rightarrow> Player \<Rightarrow> GameController"
where
	"MakeGameController p1   p2 \<equiv> 
	\<comment>\<open>User defined body of MakeGameController.\<close>
	\<lparr>Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = p1, Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = p2\<rparr>"

	
	
\<comment>\<open>VDM source: Reset: (Player * Player -> GameController)
	Reset(p1, p2) ==
mk_GameController(ResetPlayer(p1), ResetPlayer(p2))
	post ((((RESULT.Attacker).Points) = 0) and (((RESULT.Defender).Points) = 0))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 20:1\<close>

\<comment>\<open>VDM source: pre_Reset: (Player * Player +> bool)
	pre_Reset(p1, p2) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 20:1\<close>
definition
	pre_Reset :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_Reset p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Reset` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_Reset: (Player * Player * GameController +> bool)
	post_Reset(p1, p2, RESULT) ==
((((RESULT.Attacker).Points) = 0) and (((RESULT.Defender).Points) = 0))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 22:33\<close>
definition
	post_Reset :: "Player \<Rightarrow> Player \<Rightarrow> GameController \<Rightarrow> bool"
where
	"post_Reset p1   p2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_Reset` specification.\<close>
		(pre_Reset p1  p2 \<longrightarrow> (inv_Player p1  \<and>  inv_Player p2  \<and>  inv_GameController RESULT))  \<and> 
		\<comment>\<open>User defined body of post_Reset.\<close>
		(((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r RESULT)) = (0::VDMNat)) \<and> ((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r RESULT)) = (0::VDMNat)))"

definition
	Reset :: "Player \<Rightarrow> Player \<Rightarrow> GameController"
where
	"Reset p1   p2 \<equiv> 
	\<comment>\<open>User defined body of Reset.\<close>
	\<lparr>Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = (Player.ResetPlayer p1), Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = (Player.ResetPlayer p2)\<rparr>"

	
	
\<comment>\<open>VDM source: nat2strRec: (nat * seq of (char) -> seq of (char))
	nat2strRec(n, acc) ==
(if (n < 10)
then (NAT_STR((n + 1)) ^ acc)
else nat2strRec((n div 10), (NAT_STR(((n mod 10) + 1)) ^ acc)))
	measure n\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 24:1\<close>

\<comment>\<open>VDM source: pre_nat2strRec: (nat * seq of (char) +> bool)
	pre_nat2strRec(n, acc) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 24:1\<close>
definition
	pre_nat2strRec :: "VDMNat \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"pre_nat2strRec n   acc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_nat2strRec` specification.\<close>
		((inv_VDMNat n)  \<and>  (inv_VDMSeq' (inv_VDMChar) acc))"


\<comment>\<open>VDM source: post_nat2strRec: (nat * seq of (char) * seq of (char) +> bool)
	post_nat2strRec(n, acc, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 24:1\<close>
definition
	post_nat2strRec :: "VDMNat \<Rightarrow> VDMChar VDMSeq \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_nat2strRec n   acc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_nat2strRec` specification.\<close>
		(pre_nat2strRec n  acc \<longrightarrow> ((inv_VDMNat n)  \<and>  (inv_VDMSeq' (inv_VDMChar) acc)  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

fun
	nat2strRec :: "VDMNat \<Rightarrow> VDMChar VDMSeq \<Rightarrow> VDMChar VDMSeq"
where
	"nat2strRec n   acc = 
	\<comment>\<open>User defined body of nat2strRec.\<close>
	(
		if ((n < (10::VDMNat1))) then
		(((NAT_STR$(n + (1::VDMNat1))) @ acc))
		else
		((nat2strRec (n vdmdiv (10::VDMNat1))  ((NAT_STR$((n vdmmod (10::VDMNat1)) + (1::VDMNat1))) @ acc))))"

	
	
\<comment>\<open>VDM source: nat2str: (nat -> seq of (char))
	nat2str(n) ==
nat2strRec(n, [])\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 29:1\<close>

\<comment>\<open>VDM source: pre_nat2str: (nat +> bool)
	pre_nat2str(n) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 29:1\<close>
definition
	pre_nat2str :: "VDMNat \<Rightarrow> bool"
where
	"pre_nat2str n \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_nat2str` specification.\<close>
		((inv_VDMNat n))"


\<comment>\<open>VDM source: post_nat2str: (nat * seq of (char) +> bool)
	post_nat2str(n, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 29:1\<close>
definition
	post_nat2str :: "VDMNat \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_nat2str n   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_nat2str` specification.\<close>
		(pre_nat2str n \<longrightarrow> ((inv_VDMNat n)  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	nat2str :: "VDMNat \<Rightarrow> VDMChar VDMSeq"
where
	"nat2str n \<equiv> 
	\<comment>\<open>User defined body of nat2str.\<close>
	(nat2strRec n  [])"
	
\<comment>\<open>VDM source: AnnounceWinner: (Player -> seq of (char))
	AnnounceWinner(p) ==
(((("The winner is " ^ (p.Name)) ^ " with ") ^ nat2str((len ((p.GuessHist).Coords)))) ^ " guesses!
")\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 32:1\<close>

\<comment>\<open>VDM source: pre_AnnounceWinner: (Player +> bool)
	pre_AnnounceWinner(p) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 32:1\<close>
definition
	pre_AnnounceWinner :: "Player \<Rightarrow> bool"
where
	"pre_AnnounceWinner p \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_AnnounceWinner` specification.\<close>
		(inv_Player p)"


\<comment>\<open>VDM source: post_AnnounceWinner: (Player * seq of (char) +> bool)
	post_AnnounceWinner(p, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 32:1\<close>
definition
	post_AnnounceWinner :: "Player \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_AnnounceWinner p   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_AnnounceWinner` specification.\<close>
		(pre_AnnounceWinner p \<longrightarrow> (inv_Player p  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	AnnounceWinner :: "Player \<Rightarrow> VDMChar VDMSeq"
where
	"AnnounceWinner p \<equiv> 
	\<comment>\<open>User defined body of AnnounceWinner.\<close>
	(((((''The winner is '') @ (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)) @ ('' with '')) @ (nat2str (len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))))) @ ('' guesses!
''))"

	
	
\<comment>\<open>VDM source: AnnounceScore: (Player * Player -> seq of (char))
	AnnounceScore(p1, p2) ==
(((((((("Score: " ^ (p1.Name)) ^ " ") ^ nat2str((p1.Points))) ^ " - ") ^ nat2str((p2.Points))) ^ " ") ^ (p2.Name)) ^ "
")\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 36:1\<close>

\<comment>\<open>VDM source: pre_AnnounceScore: (Player * Player +> bool)
	pre_AnnounceScore(p1, p2) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 36:1\<close>
definition
	pre_AnnounceScore :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_AnnounceScore p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_AnnounceScore` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_AnnounceScore: (Player * Player * seq of (char) +> bool)
	post_AnnounceScore(p1, p2, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 36:1\<close>
definition
	post_AnnounceScore :: "Player \<Rightarrow> Player \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_AnnounceScore p1   p2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_AnnounceScore` specification.\<close>
		(pre_AnnounceScore p1  p2 \<longrightarrow> (inv_Player p1  \<and>  inv_Player p2  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	AnnounceScore :: "Player \<Rightarrow> Player \<Rightarrow> VDMChar VDMSeq"
where
	"AnnounceScore p1   p2 \<equiv> 
	\<comment>\<open>User defined body of AnnounceScore.\<close>
	(((((((((''Score: '') @ (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1)) @ ('' '')) @ (nat2str (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1))) @ ('' - '')) @ (nat2str (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p2))) @ ('' '')) @ (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p2)) @ (''
''))"

	
	
\<comment>\<open>VDM source: GameOver: (GameController -> seq of (char))
	GameOver(gc) ==
let w:Player = (gc.Defender), l:Player = (gc.Attacker) in (AnnounceWinner(w) ^ AnnounceScore(w, l))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 40:1\<close>

\<comment>\<open>VDM source: pre_GameOver: (GameController +> bool)
	pre_GameOver(gc) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 40:1\<close>
definition
	pre_GameOver :: "GameController \<Rightarrow> bool"
where
	"pre_GameOver gc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_GameOver` specification.\<close>
		(inv_GameController gc)"


\<comment>\<open>VDM source: post_GameOver: (GameController * seq of (char) +> bool)
	post_GameOver(gc, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 40:1\<close>
definition
	post_GameOver :: "GameController \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_GameOver gc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_GameOver` specification.\<close>
		(pre_GameOver gc \<longrightarrow> (inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	GameOver :: "GameController \<Rightarrow> VDMChar VDMSeq"
where
	"GameOver gc \<equiv> 
	\<comment>\<open>User defined body of GameOver.\<close>
	(
		let 
(w::Player) = (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)
		;
		
(l::Player) = (Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)
		in
			
			(if (inv_Player  w)
	 \<and> 
	(inv_Player  l) then
			((AnnounceWinner w) @ (AnnounceScore w  l))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: StartMeasure: (GameController * seq of (nat) -> nat)
	StartMeasure(gc, movesLeft) ==
let nGuesses:nat = ((len (((gc.Attacker).GuessHist).Coords)) + (len (((gc.Defender).GuessHist).Coords))) in (MAX_TOTAL_GUESSES - nGuesses)\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 44:1\<close>

\<comment>\<open>VDM source: pre_StartMeasure: (GameController * seq of (nat) +> bool)
	pre_StartMeasure(gc, movesLeft) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 44:1\<close>
definition
	pre_StartMeasure :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_StartMeasure gc   movesLeft \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_StartMeasure` specification.\<close>
		(inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft))"


\<comment>\<open>VDM source: post_StartMeasure: (GameController * seq of (nat) * nat +> bool)
	post_StartMeasure(gc, movesLeft, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 44:1\<close>
definition
	post_StartMeasure :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_StartMeasure gc   movesLeft   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_StartMeasure` specification.\<close>
		(pre_StartMeasure gc  movesLeft \<longrightarrow> (inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft)  \<and>  (inv_VDMNat RESULT)))"

definition
	StartMeasure :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMNat"
where
	"StartMeasure gc   movesLeft \<equiv> 
	\<comment>\<open>User defined body of StartMeasure.\<close>
	(
		let 
(nGuesses::VDMNat) = ((len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)))) + (len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)))))
		in
			
			(if ((inv_VDMNat nGuesses)) then
			(GLOBAL.MAX_TOTAL_GUESSES - nGuesses)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: Start: (GameController * seq of (nat) -> seq of (char))
	Start(gc, movesLeft) ==
(if (movesLeft = [])
then GameOver(gc)
else (if (((gc.Defender).Points) < N_SHIPS)
then let mk_(a, d):(Player * Player) = TakeTurn((gc.Attacker), (gc.Defender)) in Start(mk_GameController(d, a), (tl movesLeft))
else GameOver(gc)))
	measure StartMeasure\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 49:1\<close>

\<comment>\<open>VDM source: pre_Start: (GameController * seq of (nat) +> bool)
	pre_Start(gc, movesLeft) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 49:1\<close>
definition
	pre_Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_Start gc   movesLeft \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Start` specification.\<close>
		(inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft))"


\<comment>\<open>VDM source: post_Start: (GameController * seq of (nat) * seq of (char) +> bool)
	post_Start(gc, movesLeft, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 49:1\<close>
definition
	post_Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_Start gc   movesLeft   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Start` specification.\<close>
		(pre_Start gc  movesLeft \<longrightarrow> (inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft)  \<and>  (inv_VDMSeq' (inv_VDMChar) RESULT)))"

fun
	Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> VDMChar VDMSeq"
where
	"Start gc   movesLeft = 
	\<comment>\<open>User defined body of Start.\<close>
	(
		if ((movesLeft = [])) then
		((GameOver gc))
		else
		((
		if (((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)) < GLOBAL.N_SHIPS)) then
		((
		let 
	\<comment>\<open>Implicit pattern context projection for `let-bind definition`\<close>
	
(dummy0::(Player \<times> Player)) = (Player.TakeTurn (Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)  (Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc))
		in
			\<comment>\<open>Implicit pattern context projection for `pattern list`\<close>
	 let a = (fst dummy0); d = (snd dummy0) in 
			(if (
		( (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 (((inv_VDMSeq' inv_Ship (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) )\<and>
		  (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0)))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0)))) \<and> 
		 (((inv_VDMSeq' inv_Ship (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 ( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) )) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) )
		)) then
			(Start \<lparr>Attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = d, Defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = a\<rparr>  (tl movesLeft))
		 else
			undefined
		)
		))
		else
		((GameOver gc)))))"



end