abstract sig Couple {
	husband	: MaleName,
	wife	: FemaleName,
	surname	: SurName,
	animal	: Animal,
	bird	: Bird
}
enum SurName { Connor, Carver, Jones, Porter, White }
enum MaleName{ Paul, Peter, Jim, Tom, Mike }
enum FemaleName { Joanna, Marjorie, Olivia, Patricia, Sandra }
enum Animal { Beaver, Rabbit, Coyote, Woodchuck, Fox }
enum Bird { Eagle, Goose, Pheasant, Swan, WildTurkey }

fact One_to_One_Mappings {
	// Ensure that the relations under Couple are 1-1
	Couple.husband = MaleName
	Couple.wife = FemaleName
	Couple.surname = SurName
	Couple.animal = Animal
	Couple.bird = Bird
}

//Tom, who wasn’t married to Olivia, saw a fox.
//The couple that saw the beaver also saw wild turkeys. 
fact F1 {
	husband.Tom.wife != Olivia
	husband.Tom.animal = Fox
	animal.Beaver.bird = WildTurkey
}

//Patricia Carver didn’t see the pheasant. Paul didn’t see the eagle. 
//The Jones’s saw a coyote. Jim’s last name wasn’t White.
fact F2 {
	wife.Patricia.surname = Carver
	wife.Patricia.bird != Pheasant
	husband.Paul.bird != Eagle
	surname.Jones.animal = Coyote
	husband.Jim.surname != White
}

//The Porters didn’t see the swans. 
//Tom wasn’t married to Sandra and his last namewasn’t Jones. 
//The Connors spotted a rabbit. 
fact F3 {
	surname.Porter.bird != Swan
	husband.Tom.wife != Sandra
	husband.Tom.surname != Jones
	surname.Connor.animal = Rabbit
}

//The couple who saw the coyote didn’t see the swan. 
//Mike, whose last name wasn’t Connor, didn’t see the woodchuck. 
//Sandra saw the gooses.
fact F4 {
	animal.Coyote.bird = Swan
	husband.Mike.surname != Connor
	husband.Mike.animal != Woodchuck
	wife.Sandra.bird = Goose
}
//Peter and his wife Joanna didn’t see the wild turkeys. 
//Jim, whose last name wasn’t Jones, saw the pheasant but not the woodchuck. 
fact F5 {
	husband.Peter.wife = Joanna
	husband.Peter.bird != WildTurkey
	husband.Jim.surname != Jones
	husband.Jim.bird = Pheasant
	husband.Jim.animal != Woodchuck
}

//Marjorie White didn’t see the swans.
//Paul Porter didn’t see the beaver. 
fact F6 {
	wife.Marjorie.surname = White
	wife.Marjorie.bird != Swan
	husband.Paul.surname = Porter
	husband.Paul.animal != Beaver
}

run { } for 5
