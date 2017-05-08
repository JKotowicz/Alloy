sig Field extends Game {}
sig Date extends Game {}
sig Game {
	where : one Field,
	when  : one Date 
}
sig FieldComplex {
	schedule : set Game
}


//Games *not* on the schedule have no associated field or date.
fact NotOnSchedule{
	all g : Game | (no g.where or no g.when) => (g !in FieldComplex.schedule)
}

//Games that *are* on the schedule have one field and one date.
fact OnSchedule {
	all g : FieldComplex.schedule | (one g.where && one g.when)
}

//Games on the same field are scheduled for different dates.
fact SameField{
	all g1,g2 : FieldComplex.schedule | (g1.where = g2.where) => (g1.when != g2.when)
}

//at least one Game is on the FieldComplex schedule with a Date and Field.
pred ScheduledGame {
	some g : Game, d : Date, f : Field, fg : FieldComplex | (g in fg.schedule) => (g.where = f) && (g.when = d)
}

//at least one Game is not scheduled.
pred UnscheduledGame { 
	some g1, g2 : Game, fg : FieldComplex | (g1 != g2) => (g1 not in fg.schedule) && (g2 in fg.schedule)
}

run{
	ScheduledGame
	UnscheduledGame
} for 5
