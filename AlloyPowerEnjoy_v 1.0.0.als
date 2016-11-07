//#SIGNATURES

sig Boolean {
	value : one int
}
{value=0 or value=1}

sig Date{
	year : one Integer ,
	month : one Integer , 
	day : one Integer
}

sig Time{
	hour : one Integer ,
	minute : one Integer , 
	date : one Date
}

abstract sig PaymentMethod{
		userID: one User,
}

sig CreditCard extends PaymentMethod{
	creditCardID: one String,
	expDateID: one Date,
	valid: one Boolean
}

sig User{
	email: one String,
	password: one String,
	pmId: set PaymentMethod
	requests: set Request
}

sig Transaction{
	userID: one User,
	rentID: one Rent,
	paymMethID: one PaymentMethod,
	amount: one int
}

sig SafeArea{
	saID: one int,
	carsIn: set Car
}

sig Position {
	gspX: one String,
	gpsY: one String
}

sig Car{
	plateId: one String,
	rentable: one Boolean,
	inMaintenance: one Boolean,
	isUse: one Boolean,
	currentPosition: one Position
}

sig Request {
	carID: one Car,
	userID: one User,
	date: one Date,
	time: one Time,
	valid: one Boolean
}

sig Rent {
	requestID: one Request,
	costForMinute: one Int
	dateStart: one Date,
	timeStart: one Time,
	dateEnd: one Date,
	timeEnd: one Time
//	finished: one Boolean 
}

//#FACTS

fact OnlyOneRequestForTime{
	//each user can't have more than one valid request
	all r:Request | r.valid = 1 implies not(some r_ in (r.userID.requests - {p}) | r_.valid = 1)
}

fact PaymentOnlyAfterEndRent{
	//ad ogni noleggio terminato corrisponde una ed una sola transazione
	all r:Rent | r.finished = 1 implies (some t in Transaction | t.rentID = r and no(some t_ in Transaction | t_ != t and t_rentID = r))))
}

fact RentOnlyWithValidRequest{
	//TODO: da rivedere
	//per ogni noleggio esiste solo una richiesta valida che lo genera
	all r:Rent implies (some req in Request | r.requestID = req and no(some req_ in Request - {req}|r.requestID = req_))
}

fact 
