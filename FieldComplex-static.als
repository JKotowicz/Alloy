/**
 *	Fields and Date atoms used for scheduling games.
 */
some sig Field{}
some sig Date{}

/**
 * Scheduled games take place on a field on a given date.
 */
some sig Game {
	where	: lone Field,
	when	: lone Date
}

/**
 * There is one field complex with a schedule of games.
 */
one sig FieldComplex {
	schedule : set Game
}

/**
 * Games *not* on the schedule have no associated field
 * or date.
 */
fact NotOnSchedule_NoFieldNoDate {
	all g : Game - FieldComplex.schedule | no g.where && no g.when
}

/**
 * Games that *are* on the schedule have one field and one
 * date.
 */
fact OnSchedule_HaveFieldAndDate {
	all g : FieldComplex.schedule | one g.where && one g.when
}

/**
 * Games on the same field are scheduled for
 * different dates.
 */
fact SameFieldMeansDifferentDate {
	all disj g1, g2 : FieldComplex.schedule {
		g1.where = g2.where => g1.when != g2.when
	}
}

/**
 * Find solutions where at least one game is on
 * the schedule with a date. Note that 'some when'
 * implies 'some where' and 'some schedule' in order to
 * adhere to the facts.
 */
pred ScheduledGame{
 	some FieldComplex.schedule
	some when
}

/**
 * Find solutions where at least one game is NOT on
 * the schedule with a date.
 */
pred UnscheduledGame{
	some g : Game | g !in FieldComplex.schedule
}

run {
    ScheduledGame
	UnscheduledGame
} for 5
