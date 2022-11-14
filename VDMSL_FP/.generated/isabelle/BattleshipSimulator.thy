(* VDM to Isabelle Translation @2022-11-14T10:32:19.028Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl]
*)
theory BattleshipSimulator
imports "ArrangingStrategy" "GLOBAL" "GameController" "GuessingStrategy" "Player" "VDMToolkit" 
begin


\<comment>\<open>VDM source: MAX_GUESSES_SEQ:seq of (nat) = [1 | x in set {1, ... ,MAX_TOTAL_GUESSES}]\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 12:1\<close>
abbreviation
	MAX_GUESSES_SEQ :: "VDMNat VDMSeq"
where
	"MAX_GUESSES_SEQ \<equiv> [ (1::VDMNat1) . x \<leftarrow> sorted_list_of_set ({(1::VDMNat1)..GLOBAL.MAX_TOTAL_GUESSES}) , ((x \<in>{(1::VDMNat1)..GLOBAL.MAX_TOTAL_GUESSES})) ]"

	definition
	inv_MAX_GUESSES_SEQ :: "\<bool>"
where
	"inv_MAX_GUESSES_SEQ  \<equiv> (inv_VDMSeq' (inv_VDMNat) MAX_GUESSES_SEQ)"

	
	
	
\<comment>\<open>VDM source: DefaultGame: (() -> seq of (char))
	DefaultGame() ==
let p1:Player = MakePlayer("P1_DefaultDefault", "DefaultArranger", "DefaultGuesser"), p2:Player = MakePlayer("P2_DefaultDefault", "DefaultArranger", "DefaultGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in Start(gc, MAX_GUESSES_SEQ)\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 16:1\<close>

\<comment>\<open>VDM source: pre_DefaultGame: (() +> bool)
	pre_DefaultGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 16:1\<close>
definition
	pre_DefaultGame :: "bool"
where
	"pre_DefaultGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultGame: (seq of (char) +> bool)
	post_DefaultGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 16:1\<close>
definition
	post_DefaultGame :: "VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_DefaultGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultGame` specification.\<close>
		(pre_DefaultGame  \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	DefaultGame :: "VDMChar VDMSeq"
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
			(GameController.Start gc  MAX_GUESSES_SEQ)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: DefaultVsSearchWDefaultGame: (() -> seq of (char))
	DefaultVsSearchWDefaultGame() ==
let p1:Player = MakePlayer("P1_DefaultDefault", "DefaultArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DefaultSearch", "DefaultArranger", "SearchGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in Start(gc, MAX_GUESSES_SEQ)\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 24:1\<close>

\<comment>\<open>VDM source: pre_DefaultVsSearchWDefaultGame: (() +> bool)
	pre_DefaultVsSearchWDefaultGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 24:1\<close>
definition
	pre_DefaultVsSearchWDefaultGame :: "bool"
where
	"pre_DefaultVsSearchWDefaultGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultVsSearchWDefaultGame: (seq of (char) +> bool)
	post_DefaultVsSearchWDefaultGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 24:1\<close>
definition
	post_DefaultVsSearchWDefaultGame :: "VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_DefaultVsSearchWDefaultGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultVsSearchWDefaultGame` specification.\<close>
		(pre_DefaultVsSearchWDefaultGame  \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	DefaultVsSearchWDefaultGame :: "VDMChar VDMSeq"
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
			(GameController.Start gc  MAX_GUESSES_SEQ)
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

	
	
\<comment>\<open>VDM source: DefaultVsSearchWDummyGame: (() -> seq of (char))
	DefaultVsSearchWDummyGame() ==
let p1:Player = MakePlayer("P1_DummyDefault", "DummyArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DummySearch", "DummyArranger", "SearchGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in Start(gc, MAX_GUESSES_SEQ)\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 32:1\<close>

\<comment>\<open>VDM source: pre_DefaultVsSearchWDummyGame: (() +> bool)
	pre_DefaultVsSearchWDummyGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 32:1\<close>
definition
	pre_DefaultVsSearchWDummyGame :: "bool"
where
	"pre_DefaultVsSearchWDummyGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultVsSearchWDummyGame: (seq of (char) +> bool)
	post_DefaultVsSearchWDummyGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 32:1\<close>
definition
	post_DefaultVsSearchWDummyGame :: "VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_DefaultVsSearchWDummyGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultVsSearchWDummyGame` specification.\<close>
		(pre_DefaultVsSearchWDummyGame  \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	DefaultVsSearchWDummyGame :: "VDMChar VDMSeq"
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
			(GameController.Start gc  MAX_GUESSES_SEQ)
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

	
	
\<comment>\<open>VDM source: DefaultWDummyGame: (() -> seq of (char))
	DefaultWDummyGame() ==
let p1:Player = MakePlayer("P1_DummyDefault", "DummyArranger", "DefaultGuesser") in let p2:Player = MakePlayer("P2_DummyDefault", "DummyArranger", "DefaultGuesser") in let gc:GameController = MakeGameController(ArrangeShips(p1), ArrangeShips(p2)) in Start(gc, MAX_GUESSES_SEQ)\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 40:1\<close>

\<comment>\<open>VDM source: pre_DefaultWDummyGame: (() +> bool)
	pre_DefaultWDummyGame() ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 40:1\<close>
definition
	pre_DefaultWDummyGame :: "bool"
where
	"pre_DefaultWDummyGame  \<equiv> True"


\<comment>\<open>VDM source: post_DefaultWDummyGame: (seq of (char) +> bool)
	post_DefaultWDummyGame(RESULT) ==
null\<close>
\<comment>\<open>in 'BattleshipSimulator' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\BattleshipSimulator.vdmsl) at line 40:1\<close>
definition
	post_DefaultWDummyGame :: "VDMChar VDMSeq \<Rightarrow> bool"
where
	"post_DefaultWDummyGame RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_DefaultWDummyGame` specification.\<close>
		(pre_DefaultWDummyGame  \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) RESULT)))"

definition
	DefaultWDummyGame :: "VDMChar VDMSeq"
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
			(GameController.Start gc  MAX_GUESSES_SEQ)
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