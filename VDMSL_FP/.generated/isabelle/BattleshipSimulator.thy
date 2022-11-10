(* VDM to Isabelle Translation @2022-11-10T14:49:07.713Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl]
*)
theory BattleshipSimulator
imports "ArrangingStrategy" "GLOBAL" "GameController" "GuessingStrategy" "Player" "VDMToolkit" 
begin


\<comment>\<open>VDM source: BattleShipGame = compose BattleShipGame of p1:Player, p2:Player, gc:GameController, arng1:ArngType, arng2:ArngType, gues1:GuesType, gues2:GuesType end\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 12:1\<close>
record BattleShipGame = 
		p1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "Player"
		 
		 p2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "Player"
		 
		 gc\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "GameController"
		 
		 arng1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "ArngType"
		 
		 arng2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "ArngType"
		 
		 gues1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "GuesType"
		 
		 gues2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e :: "GuesType"
		

\<comment>\<open>VDM source: inv_BattleShipGame: (BattleShipGame +> bool)
	inv_BattleShipGame(dummy0) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 12:1\<close>
definition
	inv_BattleShipGame :: "BattleShipGame \<Rightarrow> bool"
where
	"inv_BattleShipGame dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_BattleShipGame` specification.\<close>
		( ((inv_Player (p1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0)) \<and> 
		 (inv_Player (p2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0)) \<and> 
		 (inv_GameController (gc\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0)) \<and> 
		 ((inv_ArngType (arng1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0))) \<and> 
		 ((inv_ArngType (arng2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0))) \<and> 
		 ((inv_GuesType (gues1\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0))) \<and> 
		 ((inv_GuesType (gues2\<^sub>B\<^sub>a\<^sub>t\<^sub>t\<^sub>l\<^sub>e\<^sub>S\<^sub>h\<^sub>i\<^sub>p\<^sub>G\<^sub>a\<^sub>m\<^sub>e dummy0))) ))"

		
lemmas inv_BattleShipGame_defs = inv_ArngType_def inv_BattleShipGame_def inv_Coordinates_def inv_GameController_def inv_Grid_def inv_GuesType_def inv_GuessHistory_def inv_GuessResult_def inv_Player_def inv_Ship_def inv_ShipT_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: GameResult = compose GameResult of name:seq of (char), p1name:seq of (char), p1points:nat, p1nguess:nat, p2ame:seq of (char), p2points:nat, p2nguess:nat end\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 21:1\<close>
record GameResult = 
		name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMChar VDMSeq"
		 
		 p1name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMChar VDMSeq"
		 
		 p1points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMNat"
		 
		 p1nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMNat"
		 
		 p2ame\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMChar VDMSeq"
		 
		 p2points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMNat"
		 
		 p2nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t :: "VDMNat"
		

\<comment>\<open>VDM source: inv_GameResult: (GameResult +> bool)
	inv_GameResult(dummy0) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 21:1\<close>
definition
	inv_GameResult :: "GameResult \<Rightarrow> bool"
where
	"inv_GameResult dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_GameResult` specification.\<close>
		( (((inv_VDMSeq' (inv_VDMChar) (name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMSeq' (inv_VDMChar) (p1name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMNat (p1points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMNat (p1nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMSeq' (inv_VDMChar) (p2ame\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMNat (p2points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) \<and> 
		 ((inv_VDMNat (p2nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t dummy0))) ))"

		
lemmas inv_GameResult_defs = inv_GameResult_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs 


	
	
\<comment>\<open>VDM source: MAX_GUESSES_SEQ:seq of (nat) = [1 | x in set {1, ... ,MAX_TOTAL_GUESSES}]\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 32:1\<close>
abbreviation
	MAX_GUESSES_SEQ :: "VDMNat VDMSeq"
where
	"MAX_GUESSES_SEQ \<equiv> [ (1::VDMNat1) . x \<leftarrow> sorted_list_of_set ({(1::VDMNat1)..GLOBAL.MAX_TOTAL_GUESSES}) , ((x \<in>{(1::VDMNat1)..GLOBAL.MAX_TOTAL_GUESSES})) ]"

	definition
	inv_MAX_GUESSES_SEQ :: "\<bool>"
where
	"inv_MAX_GUESSES_SEQ  \<equiv> (inv_VDMSeq' (inv_VDMNat) MAX_GUESSES_SEQ)"

	
	
	
\<comment>\<open>VDM source: GC2GameResult: (seq of (char) * GameController -> GameResult)
	GC2GameResult(game, gc) ==
mk_GameResult(game, ((gc.attacker).Name), ((gc.attacker).Points), (card (elems (((gc.attacker).guessHist).Coords))), ((gc.defender).Name), ((gc.defender).Points), (card (elems (((gc.defender).guessHist).Coords))))\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 36:1\<close>

\<comment>\<open>VDM source: pre_GC2GameResult: (seq of (char) * GameController +> bool)
	pre_GC2GameResult(game, gc) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 36:1\<close>
definition
	pre_GC2GameResult :: "VDMChar VDMSeq \<Rightarrow> GameController \<Rightarrow> bool"
where
	"pre_GC2GameResult game   gc \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_GC2GameResult` specification.\<close>
		((inv_VDMSeq' (inv_VDMChar) game)  \<and>  inv_GameController gc)"


\<comment>\<open>VDM source: post_GC2GameResult: (seq of (char) * GameController * GameResult +> bool)
	post_GC2GameResult(game, gc, RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 36:1\<close>
definition
	post_GC2GameResult :: "VDMChar VDMSeq \<Rightarrow> GameController \<Rightarrow> GameResult \<Rightarrow> bool"
where
	"post_GC2GameResult game   gc   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_GC2GameResult` specification.\<close>
		(pre_GC2GameResult game  gc \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) game)  \<and>  inv_GameController gc  \<and>  inv_GameResult RESULT))"

definition
	GC2GameResult :: "VDMChar VDMSeq \<Rightarrow> GameController \<Rightarrow> GameResult"
where
	"GC2GameResult game   gc \<equiv> 
	\<comment>\<open>User defined body of GC2GameResult.\<close>
	\<lparr>name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = game, p1name\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)), p1points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)), p1nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (vdm_card (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (attacker\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc))))), p2ame\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)), p2points\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)), p2nguess\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t = (vdm_card (elems (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (guessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (defender\<^sub>G\<^sub>a\<^sub>m\<^sub>e\<^sub>C\<^sub>o\<^sub>n\<^sub>t\<^sub>r\<^sub>o\<^sub>l\<^sub>l\<^sub>e\<^sub>r gc)))))\<rparr>"

	
	
\<comment>\<open>VDM source: DefaultGame: (() -> GameResult)
	DefaultGame() ==
let p1:Player = MakePlayer("P1_DefaultDefault", "DefaultArranger", "DefaultGuesser"), p2:Player = MakePlayer("P2_DefaultDefault", "DefaultArranger", "DefaultGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in GC2GameResult("DefaultGame", Start(gc, MAX_GUESSES_SEQ))\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 41:1\<close>

\<comment>\<open>VDM source: pre_DefaultGame: (() +> bool)
	pre_DefaultGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 41:1\<close>
definition
	pre_DefaultGame :: "bool"
where
	"pre_DefaultGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultGame: (GameResult +> bool)
	post_DefaultGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 41:1\<close>
definition
	post_DefaultGame :: "GameResult \<Rightarrow> bool"
where
	"post_DefaultGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultGame` specification.\<close>
		(pre_DefaultGame  \<longrightarrow> (inv_GameResult RESULT))"

definition
	DefaultGame :: "GameResult"
where
	"DefaultGame  \<equiv> 
	\<comment>\<open>User defined body of DefaultGame.\<close>
	(
		let 
(p1::Player) = (Player.MakePlayer (''P1_DefaultDefault'')  (''DefaultArranger'')  (''DefaultGuesser''))
		;
		
(p2::Player) = (Player.MakePlayer (''P2_DefaultDefault'')  (''DefaultArranger'')  (''DefaultGuesser''))
		in
			
			(if (inv_Player  p1)
	 \<and> 
	(inv_Player  p2) then
			(
		let 
(gc::GameController) = (GameController.MakeGameController (Player.ArrangeShips p1)  (Player.ArrangeShips p2))
		in
			
			(if (inv_GameController  gc) then
			(GC2GameResult (''DefaultGame'')  (GameController.Start gc  MAX_GUESSES_SEQ))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: DefaultVsSearchWDefaultGame: (() -> GameResult)
	DefaultVsSearchWDefaultGame() ==
let p1:Player = MakePlayer("P1_DefaultDefault", "DefaultArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DefaultSearch", "DefaultArranger", "SearchGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in GC2GameResult("DefaultVsSearchWDefaultGame", Start(gc, MAX_GUESSES_SEQ))\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 49:1\<close>

\<comment>\<open>VDM source: pre_DefaultVsSearchWDefaultGame: (() +> bool)
	pre_DefaultVsSearchWDefaultGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 49:1\<close>
definition
	pre_DefaultVsSearchWDefaultGame :: "bool"
where
	"pre_DefaultVsSearchWDefaultGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultVsSearchWDefaultGame: (GameResult +> bool)
	post_DefaultVsSearchWDefaultGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 49:1\<close>
definition
	post_DefaultVsSearchWDefaultGame :: "GameResult \<Rightarrow> bool"
where
	"post_DefaultVsSearchWDefaultGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultVsSearchWDefaultGame` specification.\<close>
		(pre_DefaultVsSearchWDefaultGame  \<longrightarrow> (inv_GameResult RESULT))"

definition
	DefaultVsSearchWDefaultGame :: "GameResult"
where
	"DefaultVsSearchWDefaultGame  \<equiv> 
	\<comment>\<open>User defined body of DefaultVsSearchWDefaultGame.\<close>
	(
		let 
(p1::Player) = (Player.MakePlayer (''P1_DefaultDefault'')  (''DefaultArranger'')  (''DefaultGuesser''))
		in
			
			(if (inv_Player  p1) then
			(
		let 
(p2::Player) = (Player.MakePlayer (''P2_DefaultSearch'')  (''DefaultArranger'')  (''SearchGuesser''))
		in
			
			(if (inv_Player  p2) then
			(
		let 
(gc::GameController) = (GameController.MakeGameController (Player.ArrangeShips p1)  (Player.ArrangeShips p2))
		in
			
			(if (inv_GameController  gc) then
			(GC2GameResult (''DefaultVsSearchWDefaultGame'')  (GameController.Start gc  MAX_GUESSES_SEQ))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: DefaultVsSearchWDummyGame: (() -> GameResult)
	DefaultVsSearchWDummyGame() ==
let p1:Player = MakePlayer("P1_DummyDefault", "DummyArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DummySearch", "DummyArranger", "SearchGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in GC2GameResult("DefaultVsSearchWDummyGame", Start(gc, MAX_GUESSES_SEQ))\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 57:1\<close>

\<comment>\<open>VDM source: pre_DefaultVsSearchWDummyGame: (() +> bool)
	pre_DefaultVsSearchWDummyGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 57:1\<close>
definition
	pre_DefaultVsSearchWDummyGame :: "bool"
where
	"pre_DefaultVsSearchWDummyGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultVsSearchWDummyGame: (GameResult +> bool)
	post_DefaultVsSearchWDummyGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 57:1\<close>
definition
	post_DefaultVsSearchWDummyGame :: "GameResult \<Rightarrow> bool"
where
	"post_DefaultVsSearchWDummyGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultVsSearchWDummyGame` specification.\<close>
		(pre_DefaultVsSearchWDummyGame  \<longrightarrow> (inv_GameResult RESULT))"

definition
	DefaultVsSearchWDummyGame :: "GameResult"
where
	"DefaultVsSearchWDummyGame  \<equiv> 
	\<comment>\<open>User defined body of DefaultVsSearchWDummyGame.\<close>
	(
		let 
(p1::Player) = (Player.MakePlayer (''P1_DummyDefault'')  (''DummyArranger'')  (''DefaultGuesser''))
		in
			
			(if (inv_Player  p1) then
			(
		let 
(p2::Player) = (Player.MakePlayer (''P2_DummySearch'')  (''DummyArranger'')  (''SearchGuesser''))
		in
			
			(if (inv_Player  p2) then
			(
		let 
(gc::GameController) = (GameController.MakeGameController (Player.ArrangeShips p1)  (Player.ArrangeShips p2))
		in
			
			(if (inv_GameController  gc) then
			(GC2GameResult (''DefaultVsSearchWDummyGame'')  (GameController.Start gc  MAX_GUESSES_SEQ))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: DefaultWDummyGame: (() -> GameResult)
	DefaultWDummyGame() ==
let p1:Player = MakePlayer("P1_DummyDefault", "DummyArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DummyDefault", "DummyArranger", "DefaultGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in GC2GameResult("DefaultWDummyGame", Start(gc, MAX_GUESSES_SEQ))\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 65:1\<close>

\<comment>\<open>VDM source: pre_DefaultWDummyGame: (() +> bool)
	pre_DefaultWDummyGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 65:1\<close>
definition
	pre_DefaultWDummyGame :: "bool"
where
	"pre_DefaultWDummyGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultWDummyGame: (GameResult +> bool)
	post_DefaultWDummyGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 65:1\<close>
definition
	post_DefaultWDummyGame :: "GameResult \<Rightarrow> bool"
where
	"post_DefaultWDummyGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultWDummyGame` specification.\<close>
		(pre_DefaultWDummyGame  \<longrightarrow> (inv_GameResult RESULT))"

definition
	DefaultWDummyGame :: "GameResult"
where
	"DefaultWDummyGame  \<equiv> 
	\<comment>\<open>User defined body of DefaultWDummyGame.\<close>
	(
		let 
(p1::Player) = (Player.MakePlayer (''P1_DummyDefault'')  (''DummyArranger'')  (''DefaultGuesser''))
		in
			
			(if (inv_Player  p1) then
			(
		let 
(p2::Player) = (Player.MakePlayer (''P2_DummyDefault'')  (''DummyArranger'')  (''DefaultGuesser''))
		in
			
			(if (inv_Player  p2) then
			(
		let 
(gc::GameController) = (GameController.MakeGameController (Player.ArrangeShips p1)  (Player.ArrangeShips p2))
		in
			
			(if (inv_GameController  gc) then
			(GC2GameResult (''DefaultWDummyGame'')  (GameController.Start gc  MAX_GUESSES_SEQ))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"



end