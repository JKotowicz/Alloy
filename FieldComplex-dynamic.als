/**
 * The ordered Step set used to order successive states.
 */
open util/ordering[Step]
sig Step{}

/**
 *	Field and Date atoms used for scheduling games.
 */
some sig Field{}
some sig Date{}

/**
 * Scheduled games take place on a field on a given date.
 */
some sig Game {
	where	: Field -> Step,
	when	: Date -> Step
}

/**
 * There is one field complex with a schedule of games.
 */
one sig FieldComplex {
	schedule : Game -> Step
}

/**
 * Games *not* on the schedule have no associated field
 * or date.
 */
pred NotOnSchedule_NoFieldNoDate[st : Step] {
	all g : Game - FieldComplex.schedule.st | 
		(no g.where.st && no g.when.st)
}

/**
 * Games that *are* on the schedule have one field and one
 * date.
 */
pred OnSchedule_HaveFieldAndDate[st : Step] {
	all g : FieldComplex.schedule.st | 
		(one g.where.st && one g.when.st)
}

/**
 * Games on the same field are scheduled for
 * different dates.
 */
pred SameFieldMeansDifferentDates[st : Step] {
	all disj g1, g2 : FieldComplex.schedule.st {
		g1.where.st = g2.where.st => g1.when.st != g2.when.st
	}
}

/**
 * The invariant - the conjunction of all the
 * state predicates.
 */
pred Invariant[st : Step] {
	NotOnSchedule_NoFieldNoDate[st]
	OnSchedule_HaveFieldAndDate[st]
	SameFieldMeansDifferentDates[st]
}

/**
 * Find a series of states such that the when relation for the step
 * and the were relation for the step are different from those for
 * all other steps.
 */
run {
	all st : Step {
		Invariant[st]
		no st' : Step - st | 
			(when.st = when.st' || where.st = where.st')
	}
} for 4

/************* The Initial State *************/

/**
 * In the initial state there are no games scheduled.
 * There are consequences for games that must also be
 * explicitly addressed.
 */
pred init[st : Step] {
	no FieldComplex.schedule.st
	no Game.where.st && no Game.when.st
}

pred init_exists {
	some st : Step | 
		(init[st])
}

run init_exists for 4 but 1 Step

assert init_closed {
	all st : Step | 
		(init[st] => Invariant[st])
}

check init_closed for 6 but 1 Step


/************* Scheduling a Game *************/

/**
 * Schedule a new game 'g' in field 'f' at date 'd' if this
 * will not cause a conflict.
 * The new game is not currently scheduled
 * No other games are scheduled on the requested field and date.
 * The operation completes with the new game scheduled and being specifically
    assigned the field and date requested
 * Nothing else about the schedule or the other games is affected.
 */
pred scheduleGame[g : Game, f : Field, d : Date, st : Step] {

	all sG : Game {
		(sG.where.st = f) => (sG.when.st != d)
		(sG.when.st = d) => (sG.where.st != f) 
	}
	
	let st' = next[st] {
	
		all sG : Game - g {
			sG.where.st' = sG.where.st
			sG.when.st' = sG.when.st
		}

		f = g.where.st'
		d = g.when.st' 

		FieldComplex.schedule.st' = FieldComplex.schedule.st + g

	}
}

pred scheduleGame_exists {
	some g : Game, r : Field, t : Date, st : Step {
		Invariant[st]
		scheduleGame[g, r, t, st]
	}
}

run scheduleGame_exists for 4 but 2 Step

assert scheduleGame_closed {
	all g : Game, f : Field, d : Date, st : Step {
		Invariant[st] && scheduleGame[g, f, d, st] =>
			Invariant[next[st]]
	}
}

check scheduleGame_closed for 6 but 2 Step

/************* Canceling a Game *************/

/**
 * Cancel a scheduled game 'g' by removing it from the schedule:
 * This may require updating information associated with 'g'.
 *  The game is currently scheduled
 * The operation completes with the game removed from the schedule and releasing the
     assigned field and date.
 * Nothing else about the schedule or the other games is affected
 */
pred cancelGame[g : Game, st : Step] {

	let st' = next[st] {
		all cG : Game - g {
			cG.where.st' = cG.where.st
			cG.when.st' = cG.when.st
		}
		
		no g.where.st'
		no g.when.st'

		FieldComplex.schedule.st' = FieldComplex.schedule.st - g

	}
}

pred cancelGame_exists {
	some g : Game, st : Step {
		Invariant[st]
		cancelGame[g, st]
	}
}

run cancelGame_exists for 4 but 2 Step

assert cancelGame_closed {
	all g : Game, st : Step {
		Invariant[st] && cancelGame[g, st] =>
			Invariant[next[st]]
	}
}

check cancelGame_closed for 6 but 2 Step

/************* Rescheduling a Game *************/

/**
 * Reschedule (if this will not cause a conflict) a currently scheduled
 * game 'g' on its current date but on field 'f'.
 * The game is currently scheduled and assigned a field and date
 * No other games are assigned the field 'f' on game's 'g' current date.
 * The operation completes with the game being assigned the field requested.
 * The game's originally assigned date remains the same.
 * Nothing else about the schedule or the other games is affected.
 */
pred rescheduleGame[g : Game, f : Field, st : Step] {

	#g.when.st = 1
	#g.where.st = 1

	all rG : Game {
		(rG.where.st = f) => (rG.when.st != g.when.st)
		(rG.when.st = g.when.st) => (rG.where.st != f) 
	}

	let st' = next[st] {
		all rG : Game - g {
			rG.where.st' = rG.where.st
			rG.when.st' = rG.when.st
		}

		g.when.st' = g.when.st
		g.where.st' = f

		FieldComplex.schedule.st' = FieldComplex.schedule.st

	}
}

pred rescheduleGame_exists {
	some st : Step, g : Game, f : Field {
		Invariant[st]
		rescheduleGame[g, f, st]
	}
}

run rescheduleGame_exists for 4 but 2 Step

assert rescheduleGame_closed {
	all g : Game, f : Field, st : Step {
		Invariant[st] && rescheduleGame[g, f, st] =>
			Invariant[next[st]]
	}
}

check rescheduleGame_closed for 6 but 2 Step
