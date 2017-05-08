open util/ordering[Star] as st

//
// Hotel ratings.
//
enum Star { Star3, Star4, Star5 }

// Persons are identified by their first name, and they have
// a relation to their last name.
abstract sig Person {
	ln : Name
}

// We further subdivide persons into men and women.
abstract sig Woman extends Person{}
one sig Patricia, Sarah, Wendy extends Woman{}

abstract sig Man extends Person{}
one sig Michael, Joseph extends Man{}

// The last names are a simple enumeration.
enum Name{ Weaver, Windswept, Weatherby, Ontheway, Spinner }

// A hotel has a person in it and a star rating.
abstract sig Hotel{
	who : Person,
	rating : Star
}
one sig Outlook, Wayside, Meadow, FellHollows, Peaks extends Hotel{}

// Every person has a unique last name (basic problem statement).
fact UniqueLastNames {
	Person.ln = Name 
}

// We know the last names of two of the persons who are women.
// See statements 3 and 4.
fact KnownLastNamesOfWomen {
	ln.(Windswept+Weatherby) in Woman
}


// There is exactly one three star hotel (this is a subtle fact we can
// infer from statement 1).
fact OneThreeStar {
	one h : Hotel | h.rating = Star3
}

// Each hotel has one of the persons, and each person is in
// one hotel (basic problem statement fact).
fact OneHotelPerPerson {
	Hotel.who = Person 
}

// The remaining facts are simply created from the numbered
// specification lines.
//
//*** Treat the definite article "the" as meaning exactly one.
//*** Treat the indefinite articles "a" and "an" as meaning more than one.

fact F1 {
/* 1.	The Outlook Inn had a higher rating than the hotel where Patricia stayed. 
 *     The three-star hotel was not Peak's Inn.
*/
	Outlook.rating in nexts[who.Patricia.rating]
	Peaks.rating != Star3
}

fact F2 {
/* 2.	Michael's last name was Ontheway but he didn't stay at the Wayside Lodge. 
 *     Sarah, whose last name wasn't Spinner, stayed at the Outlook Inn.
*/
	Michael.ln = Ontheway
	Wayside.who != Michael
	Sarah.ln != Spinner
	Outlook.who = Sarah
}

fact F3 {
/* 3.	Ms. Windswept and Joseph both stayed at four-star hotels.
*/
	let joe_hotel = who.Joseph | joe_hotel.rating = Star4
	let windswept_hotel = who.(ln.Windswept) {
		windswept_hotel.rating = Star4
	}
}

fact F4 {
/* 4.	Ms. Weatherby stayed at the Meadow Hotel, which wasn't a five-star hotel.
*/
	let weatherby_hotel =who.(ln.Weatherby) {
		weatherby_hotel = Meadow
	}
	Meadow.rating != Star5
}

fact F5 {
/* 5.	The Wayside Lodge was a five-star hotel. Wendy's last name wasn't Weaver.
*/
	Wayside.rating = Star5
	Wendy.ln != Weaver
}

fact F6 {
/* 6.	The Fell Hollows Lodge was rated with one star less than the hotel where the
 * person whose last name was Spinner stayed.
*/
	let hotel = who.(ln.Spinner) {
		next[FellHollows.rating] = hotel.rating
	}
}

run {} for 5
