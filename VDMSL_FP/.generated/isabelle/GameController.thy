(* VDM to Isabelle Translation @2022-11-10T14:49:07.742Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl]
*)
theory GameController
imports "GLOBAL" "Player" "VDMToolkit" 
begin


\<comment>\<open>VDM source: GameController = compose GameController of attacker:Player, defender:Player end
	inv g == ((g.attacker) <> (g.defender))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 8:1\<close>
record GameController =  attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r :: "Player"
		 
		 defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r :: "Player" 

\<comment>\<open>VDM source: inv_GameController: (GameController +> bool)
	inv_GameController(g) ==
((g.attacker) <> (g.defender))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 11:25\<close>
definition
	inv_GameController :: "GameController \<Rightarrow> bool"
where
	"inv_GameController g \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_GameController` specification.\<close>
		( ((inv_Player (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g)) \<and> 
		 (inv_Player (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g)) ))  \<and> 
		\<comment>\<open>User defined body of inv_GameController.\<close>
		((attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g) \<noteq> (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r g))"
 
lemmas inv_GameController_defs = inv_ArngType_def inv_Coordinates_def inv_GameController_def inv_Grid_def inv_GuesType_def inv_GuessHistory_def inv_GuessResult_def inv_Player_def inv_Ship_def inv_ShipT_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: MakeGameController: (Player * Player -> GameController)
	MakeGameController(p1, p2) ==
mk_GameController(p1, p2)\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 14:1\<close>

\<comment>\<open>VDM source: pre_MakeGameController: (Player * Player +> bool)
	pre_MakeGameController(p1, p2) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 14:1\<close>
definition
	pre_MakeGameController :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_MakeGameController p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_MakeGameController` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_MakeGameController: (Player * Player * GameController +> bool)
	post_MakeGameController(p1, p2, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 14:1\<close>
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
	\<lparr>attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = p1, defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = p2\<rparr>"

	
	
\<comment>\<open>VDM source: Reset: (Player * Player -> GameController)
	Reset(p1, p2) ==
mk_GameController(ResetPlayer(p1), ResetPlayer(p2))
	post ((((RESULT.attacker).Points) = 0) and (((RESULT.defender).Points) = 0))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 17:1\<close>

\<comment>\<open>VDM source: pre_Reset: (Player * Player +> bool)
	pre_Reset(p1, p2) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 17:1\<close>
definition
	pre_Reset :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_Reset p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Reset` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_Reset: (Player * Player * GameController +> bool)
	post_Reset(p1, p2, RESULT) ==
((((RESULT.attacker).Points) = 0) and (((RESULT.defender).Points) = 0))\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 19:33\<close>
definition
	post_Reset :: "Player \<Rightarrow> Player \<Rightarrow> GameController \<Rightarrow> bool"
where
	"post_Reset p1   p2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_Reset` specification.\<close>
		(pre_Reset p1  p2 \<longrightarrow> (inv_Player p1  \<and>  inv_Player p2  \<and>  inv_GameController RESULT))  \<and> 
		\<comment>\<open>User defined body of post_Reset.\<close>
		(((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r RESULT)) = (0::VDMNat)) \<and> ((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r RESULT)) = (0::VDMNat)))"

definition
	Reset :: "Player \<Rightarrow> Player \<Rightarrow> GameController"
where
	"Reset p1   p2 \<equiv> 
	\<comment>\<open>User defined body of Reset.\<close>
	\<lparr>attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = (Player.ResetPlayer p1), defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = (Player.ResetPlayer p2)\<rparr>"

	
	
\<comment>\<open>VDM source: StartMeasure: (GameController * seq of (nat) -> nat)
	StartMeasure(gc, movesLeft) ==
let nGuesses:nat = ((len (((gc.attacker).guessHist).Coords)) + (len (((gc.defender).guessHist).Coords))) in (MAX_TOTAL_GUESSES - nGuesses)\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 21:1\<close>

\<comment>\<open>VDM source: pre_StartMeasure: (GameController * seq of (nat) +> bool)
	pre_StartMeasure(gc, movesLeft) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 21:1\<close>
definition
	pre_StartMeasure :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_StartMeasure gc   movesLeft \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_StartMeasure` specification.\<close>
		(inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft))"


\<comment>\<open>VDM source: post_StartMeasure: (GameController * seq of (nat) * nat +> bool)
	post_StartMeasure(gc, movesLeft, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 21:1\<close>
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
(nGuesses::VDMNat) = ((len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)))) + (len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)))))
		in
			
			(if ((inv_VDMNat nGuesses)) then
			(GLOBAL.MAX_TOTAL_GUESSES - nGuesses)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: Start: (GameController * seq of (nat) -> GameController)
	Start(gc, movesLeft) ==
(if (movesLeft = [])
then gc
else (if (((gc.defender).Points) < N_SHIPS)
then let mk_(a, d):(Player * Player) = TakeTurn((gc.attacker), (gc.defender)) in Start(mk_GameController(d, a), (tl movesLeft))
else gc))
	measure StartMeasure\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 26:1\<close>

\<comment>\<open>VDM source: pre_Start: (GameController * seq of (nat) +> bool)
	pre_Start(gc, movesLeft) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 26:1\<close>
definition
	pre_Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> bool"
where
	"pre_Start gc   movesLeft \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_Start` specification.\<close>
		(inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft))"


\<comment>\<open>VDM source: post_Start: (GameController * seq of (nat) * GameController +> bool)
	post_Start(gc, movesLeft, RESULT) ==
null\<close>
\<comment>\<open>in 'GameController' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\GameController.vdmsl) at line 26:1\<close>
definition
	post_Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> GameController \<Rightarrow> bool"
where
	"post_Start gc   movesLeft   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_Start` specification.\<close>
		(pre_Start gc  movesLeft \<longrightarrow> (inv_GameController gc  \<and>  (inv_VDMSeq' (inv_VDMNat) movesLeft)  \<and>  inv_GameController RESULT))"

fun
	Start :: "GameController \<Rightarrow> VDMNat VDMSeq \<Rightarrow> GameController"
where
	"Start gc   movesLeft = 
	\<comment>\<open>User defined body of Start.\<close>
	(
		if ((movesLeft = [])) then
		(gc)
		else
		((
		if (((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)) < GLOBAL.N_SHIPS)) then
		((
		let 
	\<comment>\<open>Implicit pattern context projection for `let-bind definition`\<close>
	
(dummy0::(Player \<times> Player)) = (Player.TakeTurn (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)  (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc))
		in
			\<comment>\<open>Implicit pattern context projection for `pattern list`\<close>
	 let a = (fst dummy0); d = (snd dummy0) in 
			(if (
		( (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 (((inv_VDMSeq' inv_Ship (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (arngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (guesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst dummy0))))) )\<and>
		  (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0)))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0)))) \<and> 
		 (((inv_VDMSeq' inv_Ship (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 ( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) )) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (arngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (guesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (snd dummy0))))) )
		)) then
			(Start \<lparr>attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = d, defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r = a\<rparr>  (tl movesLeft))
		 else
			undefined
		)
		))
		else
		(gc))))"



end