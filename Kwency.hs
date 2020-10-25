{-# LANGUAGE LambdaCase #-}
module Kwency where

import Data.Foldable
import Data.Map (Map)
import Data.MultiSet (MultiSet)
import Data.Void
import qualified Data.Map as M
import qualified Data.MultiSet as MS

data Timer dv ov tv e i o t
	= Done
	| Wait (Duration dv e t)
	| Await (Timer dv ov tv e i o t) tv (Map i (Timer dv ov tv e i o t)) (Timer dv ov tv e i o t)
	| AddOutput (Output ov o) (Timer dv ov tv e i o t)
	| Parallel (Timer dv ov tv e i o t) (Timer dv ov tv e i o t)
	| Recurse tv [Duration dv e t] [Output ov o]
	| Fix [(dv, Duration dv e t)] [(ov, Output ov o)] tv (Timer dv ov tv e i o t)
	| TCase (Timer dv ov tv e i o t) [(TPattern dv ov tv e i t, Timer dv ov tv e i o t)] tv (Timer dv ov tv e i o t)
	-- TODO: maybe DCase would be nice
	| Sequential (Timer dv ov tv e i o t) (Timer dv ov tv e i o t)
	deriving (Read, Show)

data Duration dv e t
	= Fixed t
	| Infinity
	| External e [Duration dv e t]
	| DVar dv
	deriving (Read, Show)

data Output ov o
	= Output o
	| OVar ov
	deriving (Read, Show)

data TPattern dv ov tv e i t
	= PDone
	| PWait (DPattern dv e t)
	| PAwait tv tv (Map i tv) tv
	| PAddOutput ov tv
	| PParallel tv tv
	| PSequential tv tv
	deriving (Read, Show)

data DPattern dv e t
	= PFixed t
	| PInfinity
	| PExternal e [dv]
	| PDVar
	deriving (Read, Show)

-- Like 'Parallel', but coalesces Done
parallel :: Timer dv ov tv e i o t -> Timer dv ov tv e i o t -> Timer dv ov tv e i o t
parallel Done timer = timer
parallel timer Done = timer
parallel timer timer' = Parallel timer timer'

-- Like 'Sequential', but coalesces Done
sequential :: Timer dv ov tv e i o t -> Timer dv ov tv e i o t -> Timer dv ov tv e i o t
sequential Done timer = timer
sequential timer Done = timer
sequential timer timer' = Sequential timer timer'

-- It is the caller's responsibility to call 'simplifyDone' first.
advance ::
	( Num t, Ord t
	, Monoid o, Ord o
	, Ord dv, Show dv
	, Ord ov, Show ov
	, Ord tv, Show tv
	, Eq e, Ord i
	, Monad m) =>
	(e -> [Duration Void Void t] -> m (Duration Void Void t)) ->
	t ->
	Timer dv ov tv e i o t ->
	m (Map t (MultiSet o), Timer dv ov tv e i o t)
advance evalE t timer
	| t <= 0 = pure $ (M.empty, timer)
	| otherwise = snd <$> go M.empty M.empty M.empty t timer
		where
		go denv oenv tenv t = \timer -> case timer of
			Done -> pure (t, (M.empty, timer))
			Wait dur -> advanceDuration t <$> evalDuration evalE denv dur
			Await timer0 tv pats timerNoInput -> do
				(t1, (os, timer1)) <- go denv oenv tenv t timer0
				-- this pattern match relies on the invariant (preserved by
				-- advance) that timers that are equivalent to Done are
				-- actually returned as Done (and not as, say, Parallel Done
				-- Done)
				case timer1 of
					Done
						| t1 <= 0 -> pure (t1, (os, timerNoInput))
						| otherwise -> do
							(t3, (os', timer3)) <- go denv oenv (M.insert tv (Done, [], []) tenv) t1 timerNoInput
							pure (t3, (M.unionWith MS.union os os', timer3))
					_ -> pure (t1, (os, timer1))
			AddOutput out timer' -> do
				o <- resolveOutput oenv out
				(t', (os, timer'')) <- go denv oenv tenv t timer'
				pure (t', (MS.map (o<>) <$> os, timer''))
			Parallel timer0 timer1 -> do
				(t0, (os0, timer0')) <- go denv oenv tenv t timer0
				(t1, (os1, timer1')) <- go denv oenv tenv t timer1
				-- this preserves the invariant that timers that are equivalent
				-- to Done are actually returned as Done (and not as, say,
				-- Parallel Done Done)
				pure (min t0 t1, (M.unionWith MS.union os0 os1, parallel timer0' timer1'))
			Recurse tv durs os -> case M.lookup tv tenv of
				Just (timer', dvs, ovs) -> do
					edurs <- traverse (evalDuration evalE denv) durs
					eos <- traverse (resolveOutput oenv) os
					let denv' = M.fromList (zip dvs edurs)
					    oenv' = M.fromList (zip ovs eos)
					go (M.union denv' denv) (M.union oenv' oenv) tenv t timer'
				Nothing -> fail $ "Timer variable " ++ show tv ++ " out of scope"
			Fix dbinds obinds tv timer' -> go denv oenv tenv' t (Recurse tv durs os) where
				tenv' = M.insert tv (timer', dvs, ovs) tenv
				(dvs, durs) = unzip dbinds
				(ovs, os) = unzip obinds
			TCase timer tbinds tv timerFallthrough -> do
				(denv', oenv', tenv', timer') <- expand denv oenv tenv timer
				checkBinds denv' oenv' tenv' timer' tbinds
				where
				-- TODO: this duplicates a lot of code from the evaluation
				-- rules above; coalesce to a single function
				expand denv oenv tenv timer = case timer of
					Recurse tv durs os -> case M.lookup tv tenv of
						(Just (timer', dvs, ovs)) -> do
							edurs <- traverse (evalDuration evalE denv) durs
							eos <- traverse (resolveOutput oenv) os
							let denv' = M.fromList (zip dvs edurs)
							    oenv' = M.fromList (zip ovs eos)
							expand (M.union denv' denv) (M.union oenv' oenv) tenv timer'
						Nothing -> fail $ "Timer variable " ++ show tv ++ " out of scope"
					Fix dbinds obinds tv timer' -> expand denv oenv tenv' (Recurse tv durs os) where
						tenv' = M.insert tv (timer', dvs, ovs) tenv
						(dvs, durs) = unzip dbinds
						(ovs, os) = unzip obinds
					_ -> pure (denv, oenv, tenv, timer)

				checkBinds denv oenv tenv timer [] = go denv oenv (M.insert tv (timer, [], []) tenv) t timerFallthrough
				checkBinds denv oenv tenv timer ((tpat, timer'):tbinds) = case (tpat, timer) of
					(PDone, Done) -> go denv oenv tenv t timer'
					(PWait (PFixed tp), Wait (Fixed ta)) | tp == ta -> go denv oenv tenv t timer'
					(PWait PInfinity, Wait Infinity) -> go denv oenv tenv t timer'
					(PWait (PExternal ep dvs), Wait (External ea durs)) | ep == ea && length dvs == length durs -> do
						edurs <- traverse (evalDuration evalE denv) durs
						let denv' = M.fromList (zip dvs edurs)
						go (M.union denv' denv) oenv tenv t timer'
					(PWait PDVar, Wait (DVar _)) -> go denv oenv tenv t timer'
					(PAwait tvCurrent tvCont tvIs tvDone, Await tCurrent tvCont' tIs tDone)
						| M.keysSet tvIs == M.keysSet tIs -> go denv oenv (M.union tenv' tenv) t timer' where
						tenv' = M.map (\timer -> (timer, [], []))
							$ M.fromList [(tvCurrent, tCurrent), (tvCont, Recurse tvCont' [] []), (tvDone, tDone)]
							`M.union` fold (M.intersectionWith M.singleton tvIs tIs)
					(PAddOutput ov tv, AddOutput o tOut) -> do
						eo <- resolveOutput oenv o
						go denv (M.insert ov eo oenv) (M.insert tv (tOut, [], []) tenv) t timer'
					(PParallel tvl tvr, Parallel timerl timerr) -> go denv oenv (M.union tenv tenv') t timer' where
						tenv' = M.fromList [(tvl, (timerl, [], [])), (tvr, (timerr, [], []))]
					(PSequential tv1 tv2, Sequential timer1 timer2) -> go denv oenv (M.union tenv tenv') t timer' where
						tenv' = M.fromList [(tv1, (timer1, [], [])), (tv2, (timer2, [], []))]
					_ -> checkBinds denv oenv tenv timer tbinds
			Sequential timer0 timer1 -> do
				-- this relies on the promise that the timer sent into the
				-- function is already simplified, so that timer0 isn't, say,
				-- Parallel Done Done
				(t0, (os0, timer0')) <- go denv oenv tenv t timer0
				case timer0' of
					Done
						| t0 <= 0 -> pure (t0, (os0, timer1))
						| otherwise -> do
							(t1, (os1, timer1')) <- go denv oenv tenv t0 timer1
							pure (t1, (M.unionWith MS.union os0 os1, timer1'))
					-- this relies on the promise that the timer sent into the
					-- function is already simplified (i.e. that timer1 isn't,
					-- say, Parallel Done Done); under that assumption, it
					-- preserves the invariant that timers that are equivalent
					-- to Done are actually returned as Done (and not as, say,
					-- Parallel Done Done)
					_ -> pure (t0, (os0, sequential timer0' timer1))

advanceDuration :: (Monoid o, Num t, Ord t) =>
	t ->
	Duration Void Void t ->
	(t, (Map t (MultiSet o), Timer dv ov tv e i o t))
advanceDuration t (Fixed t') = if t' > t
	then (0, (M.empty, Wait (Fixed (t' - t))))
	else (t - t', (M.singleton t' (MS.singleton mempty), Done))
advanceDuration t Infinity = (0, (M.empty, Wait Infinity))

evalDuration :: (Ord dv, Show dv, Monad m) =>
	(e -> [Duration Void Void t] -> m (Duration Void Void t)) ->
	Map dv (Duration Void Void t) ->
	Duration dv e t ->
	m (Duration Void Void t)
evalDuration evalE denv = go where
	go dur = case dur of
		Fixed t -> pure (Fixed t)
		Infinity -> pure Infinity
		External e args -> traverse go args >>= evalE e
		DVar dv -> case M.lookup dv denv of
			Nothing -> fail $ "Duration variable " ++ show dv ++ " out of scope"
			Just dur' -> pure dur'

resolveOutput :: (Ord ov, Show ov, Monad m) => Map ov o -> Output ov o -> m o
resolveOutput oenv (Output o) = pure o
resolveOutput oenv (OVar ov) = case M.lookup ov oenv of
	Just o -> pure o
	Nothing -> fail $ "Output variable " ++ show ov ++ " out of scope"

-- TODO: should we have a separate simplification for finding infinite waits
-- and simplifying constructs that have them? is it even possible to statically
-- detect when a timer is equivalent to Wait Infinity?
simplifyDone :: Timer dv ov tv e i o t -> Timer dv ov tv e i o t
simplifyDone = \case
	Done -> Done
	Wait dur -> Wait dur
	Await timer tv pats timerNoInput -> case simplifyDone timer of
		Done -> simplifyDone timerNoInput
		timer' -> Await timer' tv (fmap simplifyDone pats) (simplifyDone timerNoInput)
	AddOutput o timer -> case simplifyDone timer of
		Done -> Done
		timer' -> AddOutput o timer'
	Parallel timer0 timer1 -> parallel (simplifyDone timer0) (simplifyDone timer1)
	-- we assume here that a separate check (not yet implemented) that all the
	-- fixpoints are sensible -- have a Wait at their head -- has already
	-- passed, so that all bound variables come from either an Await (which
	-- won't be awaiting Done, hence may bind the variable to something other
	-- than Done) or a Fix, hence may not be Done at runtime
	Recurse tv ds os -> Recurse tv ds os
	Fix dbinds obinds tv timer -> case simplifyDone timer of
		Done -> Done
		timer' -> Fix dbinds obinds tv timer'
	-- the user can fool us here by adding a pattern that they know won't match
	-- at runtime (or causing the fallthrough to never get hit) and binding it
	-- to a non-Done timer
	TCase timer tbinds tv timerFallthrough -> case (fmap simplifyDone <$> tbinds, simplifyDone timerFallthrough) of
		(tbinds', Done) | all (\case (_,Done) -> True; _ -> False) tbinds' -> Done
		(tbinds', timerFallthrough') -> TCase timer tbinds' tv timerFallthrough'
	Sequential timer0 timer1 -> sequential (simplifyDone timer0) (simplifyDone timer1)
