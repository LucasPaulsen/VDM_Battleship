(* VDM to Isabelle Translation @2022-11-14T10:32:19.106Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl' at line 1:8
files = [c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl]
*)
theory Player
imports "ArrangingStrategy" "GLOBAL" "Grid" "GuessingStrategy" "VDMToolkit" 
begin


\<comment>\<open>VDM source: Player = compose Player of Name:seq of (char), Points:nat, PGrid:Grid, GuessHist:GuessHistory, ArngStrat:ArngType, GuesStrat:GuesType end
	inv p == ((p.Points) <= N_SHIPS)\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 11:1\<close>
record Player =  Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "VDMChar VDMSeq"
		 
		 Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "VDMNat"
		 
		 PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "Grid"
		 
		 GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "GuessHistory"
		 
		 ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "ArngType"
		 
		 GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r :: "GuesType" 

\<comment>\<open>VDM source: inv_Player: (Player +> bool)
	inv_Player(p) ==
((p.Points) <= N_SHIPS)\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 18:19\<close>
definition
	inv_Player :: "Player \<Rightarrow> bool"
where
	"inv_Player p \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Player` specification.\<close>
		( (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))) \<and> 
		 ((inv_Grid (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))) \<and> 
		 (inv_GuessHistory (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)) \<and> 
		 ((inv_ArngType (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))) \<and> 
		 ((inv_GuesType (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))) ))  \<and> 
		\<comment>\<open>User defined body of inv_Player.\<close>
		((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p) \<le> GLOBAL.N_SHIPS)"
 
lemmas inv_Player_defs = inv_ArngType_def inv_Coordinates_def inv_Grid_def inv_GuesType_def inv_GuessHistory_def inv_GuessResult_def inv_Player_def inv_Ship_def inv_ShipT_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq'_def inv_VDMSeq'_defs inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_bool_def 


	
	
\<comment>\<open>VDM source: MakePlayer: (seq of (char) * ArngType * GuesType -> Player)
	MakePlayer(s, a, g) ==
mk_Player(s, 0, [], mk_GLOBAL`GuessHistory([], []), a, g)\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 22:1\<close>

\<comment>\<open>VDM source: pre_MakePlayer: (seq of (char) * ArngType * GuesType +> bool)
	pre_MakePlayer(s, a, g) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 22:1\<close>
definition
	pre_MakePlayer :: "VDMChar VDMSeq \<Rightarrow> ArngType \<Rightarrow> GuesType \<Rightarrow> bool"
where
	"pre_MakePlayer s   a   g \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_MakePlayer` specification.\<close>
		((inv_VDMSeq' (inv_VDMChar) s)  \<and>  (inv_ArngType a)  \<and>  (inv_GuesType g))"


\<comment>\<open>VDM source: post_MakePlayer: (seq of (char) * ArngType * GuesType * Player +> bool)
	post_MakePlayer(s, a, g, RESULT) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 22:1\<close>
definition
	post_MakePlayer :: "VDMChar VDMSeq \<Rightarrow> ArngType \<Rightarrow> GuesType \<Rightarrow> Player \<Rightarrow> bool"
where
	"post_MakePlayer s   a   g   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_MakePlayer` specification.\<close>
		(pre_MakePlayer s  a  g \<longrightarrow> ((inv_VDMSeq' (inv_VDMChar) s)  \<and>  (inv_ArngType a)  \<and>  (inv_GuesType g)  \<and>  inv_Player RESULT))"

definition
	MakePlayer :: "VDMChar VDMSeq \<Rightarrow> ArngType \<Rightarrow> GuesType \<Rightarrow> Player"
where
	"MakePlayer s   a   g \<equiv> 
	\<comment>\<open>User defined body of MakePlayer.\<close>
	\<lparr>Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = s, Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (0::VDMNat), PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = [], GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = \<lparr>Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y = [], Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y = []\<rparr>, ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = a, GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = g\<rparr>"

	
	
\<comment>\<open>VDM source: ResetPlayer: (Player -> Player)
	ResetPlayer(p) ==
MakePlayer((p.Name), (p.ArngStrat), (p.GuesStrat))\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 25:1\<close>

\<comment>\<open>VDM source: pre_ResetPlayer: (Player +> bool)
	pre_ResetPlayer(p) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 25:1\<close>
definition
	pre_ResetPlayer :: "Player \<Rightarrow> bool"
where
	"pre_ResetPlayer p \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_ResetPlayer` specification.\<close>
		(inv_Player p)"


\<comment>\<open>VDM source: post_ResetPlayer: (Player * Player +> bool)
	post_ResetPlayer(p, RESULT) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 25:1\<close>
definition
	post_ResetPlayer :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"post_ResetPlayer p   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ResetPlayer` specification.\<close>
		(pre_ResetPlayer p \<longrightarrow> (inv_Player p  \<and>  inv_Player RESULT))"

definition
	ResetPlayer :: "Player \<Rightarrow> Player"
where
	"ResetPlayer p \<equiv> 
	\<comment>\<open>User defined body of ResetPlayer.\<close>
	(MakePlayer (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)  (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)  (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p))"

	
	
\<comment>\<open>VDM source: ArrangeShips: (Player -> Player)
	ArrangeShips(p) ==
mk_Player((p.Name), (p.Points), Arrange((p.ArngStrat)), (p.GuessHist), (p.ArngStrat), (p.GuesStrat))\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 28:1\<close>

\<comment>\<open>VDM source: pre_ArrangeShips: (Player +> bool)
	pre_ArrangeShips(p) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 28:1\<close>
definition
	pre_ArrangeShips :: "Player \<Rightarrow> bool"
where
	"pre_ArrangeShips p \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_ArrangeShips` specification.\<close>
		(inv_Player p)"


\<comment>\<open>VDM source: post_ArrangeShips: (Player * Player +> bool)
	post_ArrangeShips(p, RESULT) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 28:1\<close>
definition
	post_ArrangeShips :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"post_ArrangeShips p   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ArrangeShips` specification.\<close>
		(pre_ArrangeShips p \<longrightarrow> (inv_Player p  \<and>  inv_Player RESULT))"

definition
	ArrangeShips :: "Player \<Rightarrow> Player"
where
	"ArrangeShips p \<equiv> 
	\<comment>\<open>User defined body of ArrangeShips.\<close>
	\<lparr>Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (ArrangingStrategy.Arrange (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)), GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)\<rparr>"

	
	
\<comment>\<open>VDM source: ReceiveGuess: (Player * Coordinates -> (Player * GuessResult))
	ReceiveGuess(p, c) ==
let gr:(Grid * GuessResult) = Hit((p.PGrid), c) in mk_(mk_Player((p.Name), (p.Points), (gr.#1), (p.GuessHist), (p.ArngStrat), (p.GuesStrat)), (gr.#2))\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 31:1\<close>

\<comment>\<open>VDM source: pre_ReceiveGuess: (Player * Coordinates +> bool)
	pre_ReceiveGuess(p, c) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 31:1\<close>
definition
	pre_ReceiveGuess :: "Player \<Rightarrow> Coordinates \<Rightarrow> bool"
where
	"pre_ReceiveGuess p   c \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_ReceiveGuess` specification.\<close>
		(inv_Player p  \<and>  inv_Coordinates c)"


\<comment>\<open>VDM source: post_ReceiveGuess: (Player * Coordinates * (Player * GuessResult) +> bool)
	post_ReceiveGuess(p, c, RESULT) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 31:1\<close>
definition
	post_ReceiveGuess :: "Player \<Rightarrow> Coordinates \<Rightarrow> (Player \<times> GuessResult) \<Rightarrow> bool"
where
	"post_ReceiveGuess p   c   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ReceiveGuess` specification.\<close>
		(pre_ReceiveGuess p  c \<longrightarrow> (inv_Player p  \<and>  inv_Coordinates c  \<and>  
		(inv_Player (fst RESULT)\<and>
		 inv_GuessResult (snd RESULT)
		)))"

definition
	ReceiveGuess :: "Player \<Rightarrow> Coordinates \<Rightarrow> (Player \<times> GuessResult)"
where
	"ReceiveGuess p   c \<equiv> 
	\<comment>\<open>User defined body of ReceiveGuess.\<close>
	(
		let 
(gr::(Grid \<times> GuessResult)) = (Grid.Hit (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)  c)
		in
			
			(if (
		(((inv_VDMSeq' inv_Ship (fst gr)))\<and>
		  (((inv_bool (Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd gr)))) \<and> 
		 ((inv_bool (Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd gr)))) )
		)) then
			(\<lparr>Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (fst (gr)), GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p), GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p)\<rparr> , (snd (gr)))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: TakeTurn: (Player * Player -> (Player * Player))
	TakeTurn(p1, p2) ==
let c:Coordinates = Guess((p1.GuesStrat), (p1.GuessHist)) in let gr:(Player * GuessResult) = ReceiveGuess(p2, c) in mk_(mk_Player((p1.Name), (if ((gr.#2).Sunk)
then ((p1.Points) + 1)
else (p1.Points)), (p1.PGrid), mk_GLOBAL`GuessHistory(([c] ^ ((p1.GuessHist).Coords)), ([(gr.#2)] ^ ((p1.GuessHist).Results))), (p1.ArngStrat), (p1.GuesStrat)), (gr.#1))
	post ((len (((RESULT.#1).GuessHist).Coords)) = ((len ((p1.GuessHist).Coords)) + 1))\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 36:1\<close>

\<comment>\<open>VDM source: pre_TakeTurn: (Player * Player +> bool)
	pre_TakeTurn(p1, p2) ==
null\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 36:1\<close>
definition
	pre_TakeTurn :: "Player \<Rightarrow> Player \<Rightarrow> bool"
where
	"pre_TakeTurn p1   p2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_TakeTurn` specification.\<close>
		(inv_Player p1  \<and>  inv_Player p2)"


\<comment>\<open>VDM source: post_TakeTurn: (Player * Player * (Player * Player) +> bool)
	post_TakeTurn(p1, p2, RESULT) ==
((len (((RESULT.#1).GuessHist).Coords)) = ((len ((p1.GuessHist).Coords)) + 1))\<close>
\<comment>\<open>in 'Player' (c:\Users\Lenovo\OneDrive - Aarhus Universitet\Speciale\Battleship\DEV\Player.vdmsl) at line 49:37\<close>
definition
	post_TakeTurn :: "Player \<Rightarrow> Player \<Rightarrow> (Player \<times> Player) \<Rightarrow> bool"
where
	"post_TakeTurn p1   p2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_TakeTurn` specification.\<close>
		(pre_TakeTurn p1  p2 \<longrightarrow> (inv_Player p1  \<and>  inv_Player p2  \<and>  
		(inv_Player (fst RESULT)\<and>
		 inv_Player (snd RESULT)
		)))  \<and> 
		\<comment>\<open>User defined body of post_TakeTurn.\<close>
		((len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst (RESULT))))) = ((len (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1))) + (1::VDMNat1)))"

definition
	TakeTurn :: "Player \<Rightarrow> Player \<Rightarrow> (Player \<times> Player)"
where
	"TakeTurn p1   p2 \<equiv> 
	\<comment>\<open>User defined body of TakeTurn.\<close>
	(
		let 
(c::Coordinates) = (GuessingStrategy.Guess (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1)  (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1))
		in
			
			(if (inv_Coordinates  c) then
			(
		let 
(gr::(Player \<times> GuessResult)) = (ReceiveGuess p2  c)
		in
			
			(if (
		( (((inv_VDMSeq' (inv_VDMChar) (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr)))) \<and> 
		 ((inv_VDMNat (Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr)))) \<and> 
		 (((inv_VDMSeq' inv_Ship (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr))))) \<and> 
		 ( (((inv_VDMSeq' inv_Coordinates  (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr))))) \<and> 
		 ((inv_VDMSeq' inv_GuessResult  (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr))))) )) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr))))) \<and> 
		 (((inv_VDMSeq' (inv_VDMChar) (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r (fst gr))))) )\<and>
		  (((inv_bool (Hit\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd gr)))) \<and> 
		 ((inv_bool (Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd gr)))) )
		)) then
			(\<lparr>Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (Name\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1), Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = ( if ((Sunk\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>R\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t (snd (gr)))) then (((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1) + (1::VDMNat1))) else ((Points\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1))), PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (PGrid\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1), GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = \<lparr>Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y = ([c] @ (Coords\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1))), Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y = ([(snd (gr))] @ (Results\<^sub>G\<^sub>u\<^sub>e\<^sub>s\<^sub>s\<^sub>H\<^sub>i\<^sub>s\<^sub>t\<^sub>o\<^sub>r\<^sub>y (GuessHist\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1)))\<rparr>, ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (ArngStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1), GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r = (GuesStrat\<^sub>P\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r p1)\<rparr> , (fst (gr)))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"



end