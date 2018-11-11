open util/boolean

//As in UNIX, time is represented as an offset in seconds
//from midnight (UTC) on January 1, 1970.

//String abstraction
sig StringTM {}

//SIGNATURES

//Standard user
sig StandardUser
{
	email: one StringTM,
	name: one StringTM,
	surname: one StringTM,
	dateOfBirth: one Int,
	address: one Address,
	occupation: one Occupation,
	smartphone: set Smartphone,
}

//Special user
sig SpecialUser
{
	corporateEmail: one StringTM,
	businessName: one StringTM,
	vat: one Int,
	referentsSurname: one StringTM,
	referentName: one StringTM,
	legalAddress: one Address,
	billingAddress: one Address,
	sector: one Sector,
}

//Position
sig Position
{
	latitude: one Int,
	longitude: one Int,
}

//Abstract data request
abstract sig DataRequest
{
	accepted: one Bool,
	date: one Int,
	nDownload: one Int,
	applicant: one SpecialUser,
	payment: lone Payment,
}
{
	one payment implies accepted=True
	nDownload>=0
}

//Request for single user data
sig SingleUserDataRequest extends DataRequest
{
	target: one StandardUser,
}

//Request for group data
sig GroupDataRequest extends DataRequest
{
	target: set StandardUser,
}

//Address
sig Address
{
	country: one StringTM,
	province: one StringTM,
	city: one StringTM,
	street: one StringTM,
	houseNumber: one Int,
}
{
	houseNumber>0
}

//Data of a run
sig Run
{
	runID: one Int,
	name: one StringTM,
	organizer: one StandardUser,
	partecipants: set StandardUser,
	route: set Position,
	city: one StringTM,
	date: one Int,
	regDeadline: one Int,
}
{
	regDeadline<=date
}

//Registration to a Run
sig RunRegistration
{
	runner: one StandardUser,
	registration: one Run,
	date: one Int,
}

//Smartphone
sig Smartphone
{
	smartphoneID: one Int,
	bluetoothConnection: one Bool,
	isWorking: one Bool,
	batteryLevel: one BatteryLevel,
	isOnCharge: one Bool,
	records: set PositionRecord,
	sosCall: set SOSCall,
	device: set Device,
}
{
	isWorking=True implies not (batteryLevel=Empty)
	bluetoothConnection=True implies not (batteryLevel=Empty)
	batteryLevel=Empty implies bluetoothConnection=False
	batteryLevel=Empty implies isWorking=False
	isWorking=True implies (some records)
}

//SOSCall
sig SOSCall
{
	callID: one Int,
	date: one Int,
}

//Device
sig Device
{
	deviceID: one Int,
	bluetoothConnection: one Bool,
	isWorking: one Bool,
	batteryLevel: one BatteryLevel,
	isOnCharge: one Bool,
	records: set HealthStatusRecord,
}
{
	isWorking=True implies not (batteryLevel=Empty)
	bluetoothConnection=True implies not (batteryLevel=Empty)
	batteryLevel=Empty implies bluetoothConnection=False
	batteryLevel=Empty implies isWorking=False
}

//Position Record
sig PositionRecord
{
	time: one Int,
	position: one Position,
}

//Health Status Record
sig HealthStatusRecord
{
	time: one Int,
	healthStatus: one HealthStatus,
}

//Health Status
sig HealthStatus
{
	minPressure: one Int,
	maxPressure: one Int,
	heartbeat: one Int,
	health: one Health,
}
{
	maxPressure>=minPressure
	maxPressure>=0
	minPressure>=0
	heartbeat>=0
}

//Payment
sig Payment
{
	amount: one Int,
	date: one Int,
}
{
	amount>=0
}

//Enum BatteryLevel
abstract sig BatteryLevel {}
	one sig Empty extends BatteryLevel{}
	one sig Low extends BatteryLevel{}
	one sig Medium extends BatteryLevel{}
	one sig High extends BatteryLevel{}

//Enum Job Sector
abstract sig Sector {}
	one sig Finance extends Sector{}
	one sig Business extends Sector{}
	one sig Pharmaceutical extends Sector{}
	one sig Engineering extends Sector{}
	one sig Environment extends Sector{}
	one sig Healthcare extends Sector{}
	one sig IT extends Sector{}
	one sig Law extends Sector{}

//Enum User Occupation
abstract sig Occupation {}
	one sig Student extends Occupation {}
	one sig Employed extends Occupation{}
	one sig Unemployed extends Occupation{}

//Enum User Health
abstract sig Health {}
	one sig Good extends Health{}
	one sig Bad extends Health{}


//FACTS


// Users can't have the same email address
fact usersCannotHaveTheSameEmailAddress
{
	no u1, u2 : StandardUser | u1.email=u2.email and u1!=u2
	no u1, u2 : SpecialUser | u1.corporateEmail=u2.corporateEmail
		and u1!=u2
	no u1 : StandardUser, u2 : SpecialUser |
		u1.email = u2.corporateEmail
}

//No runs with same runID
fact noRunsSameID
{
	no r1, r2 : Run | r1.runID=r2.runID and r1!=r2
}

//Bad health status implies a SOSCall within 5 seconds
fact badHealthStatusImpliesASOSCallWithin5Seconds
{
	all h : HealthStatusRecord | h.healthStatus.health=Bad
		implies (one c : SOSCall, u : StandardUser | c.date>=h.time
			and c.date<=h.time+5 and c in u.smartphone.sosCall)
}

//No two SOSCall in the same moment for the same user
fact noTwoSOSCallInSameMomentSameUser
{
	no c1, c2 : SOSCall, u1 : StandardUser | c1.date=c2.date
		and c1 in (u1.smartphone.sosCall)
			and c2 in (u1.smartphone.sosCall)
}

//No two or more SOSCall with same IDCAll
fact noMoreSOSCallWithSameID
{
	no c1, c2 : SOSCall | c1.callID=c2.callID and c1!=c2
}

//All SOSCalls have Bad health status record
fact allSOSCallWithABadHealthStatusRecord
{
	all  c : SOSCall, u : StandardUser | c in u.smartphone.sosCall
	implies (one h : HealthStatusRecord, u : StandardUser |
		h.healthStatus.health=Bad and c.date=h.time
			and h in u.smartphone.device.records)
}

//All group data requests with more than 999 users are accepted
fact allGroupDataRequest1000UsersOrMoreAreAccepted
{
	all r : GroupDataRequest | #r.target>=1000
		implies r.accepted=True
}

//All group data request for less than 1000 users are not accepted
fact allGroupRequestForLessThan999UserNotAccepted
{
	all r : GroupDataRequest | #r.target<1000
		implies r.accepted=False
}

//Only accepted group data request can be payed
fact OnlyAcceptedGroupDataRequestCanBePayed
{
	all p : Payment, r : GroupDataRequest | r.payment=p
		implies r.accepted=True
}

//Only accepted single user request can be payed
fact OnlyAcceptedSingleUserDataRequestCanBePayed
{
	all p : Payment, r : SingleUserDataRequest | r.payment=p
		implies r.accepted=True
}

//All saved addresses refer to a user
fact allSavedAddressesReferToAUser
{
	all a : Address, u1 : SpecialUser, u2 : StandardUser |
		a not in u1.legalAddress implies (a in u1.billingAddress
			or a in u2.address)
	all a : Address, u1 : SpecialUser, u2 : StandardUser |
		a not in u1.billingAddress implies (a in u1.legalAddress
			or a in u2.address)
	all a : Address, u1 : SpecialUser, u2 : StandardUser |
		a not in u2.address implies (a in u1.billingAddress
			or a in u1.legalAddress)
}

//All payments are made only after the request has been made
fact paymentAfterRequest
{
	all p : Payment, r : DataRequest | r.payment=p
		and p.date>=r.date
}

//All downloads are possible only if the request is accepted
fact allDownloadsAfterRequestAcceptedAndPaid
{
	all r : DataRequest | r.nDownload>0
		implies r.accepted=True
}

//All downloads are possible only if the request is paid
fact allDownloadsAfterRequestAcceptedAndPaid
{
	all r : DataRequest, p : Payment | r.nDownload>0
		implies r.payment=p
}

//Smartphone is working only if it has no empty battery
fact smartphoneWorkingIfBatteryNotEmpty
{
	all s : Smartphone | s.isWorking=True
		implies s.batteryLevel!=Empty
}

//Device is working only if it has no empty battery and
//smartphone has not empty battery
//and bluetoothConnection is On
fact deviceWorkingIfBatteryNotEmpty
{
	all d : Device, s : Smartphone | d.isWorking=True
		implies (d in s.device and d.batteryLevel!=Empty
			and s.batteryLevel!=Empty
			and d.bluetoothConnection=True
			and d.bluetoothConnection=True)
}

//Max pressure over 170 implies a Bad status
fact maxPressureOver170
{
	all h : HealthStatus | h.maxPressure>170 implies h.health=Bad
}

//Min pressure under 100 implies a Bad status
fact minPressureOver170
{
	all h : HealthStatus | h.minPressure<100 implies h.health=Bad
}

//Heartbeat over 120 implies a Bad status
fact heartbeatUnder120
{
	all h : HealthStatus | h.heartbeat>120 implies h.health=Bad
}

//Heartbeat under 45 implies a Bad status
fact heartbeatUnder45
{
	all h : HealthStatus | h.heartbeat<45 implies h.health=Bad
}

//Min pressure over 100 and max pressure under 170 and
//heartbeat between 45 and 120 implies Good status
fact pressureHeartbeatGoodStatus
{
	all h : HealthStatus | (h.maxPressure<=170
		and h.minPressure>=100
		and h.heartbeat>=45 and h.heartbeat<=170)
			implies h.health=Good
}


//No runs with same name, date, city
fact allRunsHaveSomerthindDifferent
{
	no r1, r2 : Run | r1.name=r2.name and r1.date=r2.date
		and r1.city=r2.city and r1!=r2
}

//Registration before registration deadline
fact registrationBeforeDeadline
{
	all r : RunRegistration, n : Run | r.registration=n
		implies r.date<n.regDeadline
}

//All PositionRecords refer to a Smartphone
fact positionRecordsReferToASmartphone
{
	all p : PositionRecord | one s : Smartphone | p in s.records
}

//A PositionRecord refers to only one Smartphone
fact positionRecordsReferToOnlyOneSmartphone
{
	no p : PositionRecord, s1, s2 : Smartphone |
		p in s1.records and p in s2.records
}

//All payments refer to a request
fact paymentsReferToARequest
{
	all p : Payment | one r : DataRequest | p=r.payment
}

//All Smartphones refer to a StandardUser
fact SmartphonesReferToAStandardUser
{
	all s : Smartphone | one u : StandardUser | s in u.smartphone
}

//All Devices refer to a Smartphone
fact deviceReferToASmartphone
{
	all d : Device | one s : Smartphone | d in s.device
}

//All SOSCalls refer to a Smartphone
fact sosCallsReferToASmartphone
{
	all c : SOSCall | some s : Smartphone| c in s.sosCall
}

//All Positions refer to a Run or to a PositionRecord
fact positionsReferToARunOrToAPositionRecord
{
	all p : Position | (some r : PositionRecord| p=r.position
		or some r : Run | p in r.route)
}

//All run registration for a run are for different runners
fact runRegistrationSameRunDifferentRunners
{
	all r1, r2 : RunRegistration | r1!=r2 and r1.runner=r2.runner
		implies r1.registration!=r2.registration
}


// PREDICATES


//Special users can make more than one request
pred specialUsersCanMakeMoreThanOneDataRequest
{
	some r1, r2 :  DataRequest |
		r1.applicant=r2.applicant and r1!=r2
}

//A user can partecipate in more than one run
pred usersCanPartecipateInMoreThanOneRun
{
	some r1, r2 :  RunRegistration |
		r1.runner=r2.runner and r1!=r2
}


//ASSERTIONS


//No accepted group data request with less
//than 1000 special users
assert noLessThan1000UsersInGroupDataRequests
{
	no r : GroupDataRequest | #r.target<1000
		and r.accepted=True
}

//No payment for not accepted requests
assert noPaymentForNotAcceptedSingleUserDataRequests
{
	no p : Payment, r : SingleUserDataRequest |
		p in r.payment and r.accepted=False
}

//No SOSCall without a Bad status in previous 5 seconds
assert noSOSCallWithoutBadStatus
{
	all c : SOSCall, u : StandardUser | c in u.smartphone.sosCall
		implies (one h : HealthStatusRecord |
			h in u.smartphone.device.records
			and c.date>=h.time and c.date<=h.time+5
			and h.healthStatus.health=Bad)
}

//No group request for 1000 users or more not accepted
assert noGroupRequestsMoreThan1000UsersNotAccepted
{
	no r : GroupDataRequest | #r.target>1000
		and r.accepted=False
}

//No saved addresses not used
assert noSavedAddressesNotUsed
{
	no a : Address, u1 : SpecialUser, u2: StandardUser |
		(a not in u1.legalAddress)
		and (a not in u1.billingAddress)
		and (a not in u2.address)
}

//No requests are paid before the data request
assert noPaymentBeforeRequest
{
	no p : Payment, r : DataRequest |
		r.payment=p and p.date<r.date
}

//No download before the request is accepted
assert noDownloadBeforeRequestAcceptedAndPaid
{
	all r : DataRequest, p : Payment |
		r.accepted=False or (p not in r.payment)
		implies r.nDownload=0
}

//No device isWorking if smartphone has empty battery
assert noDeviceIsWorkingIfSmartphoneHasEmptyBattery
{
	no d : Device, s : Smartphone | d in s.device
		and d.isWorking=True and s.batteryLevel=Empty
}

//No health status with max pressure lower than min pressure
assert noHealthStatusMaxPressureLowerThanMinPressure
{
	no h: HealthStatus | h.maxPressure<h.minPressure
}

//No Good health status with Bad values
assert noGoodHealthStatusWithBadValues
{
	no h: HealthStatus | h.health=Good
		and (h.maxPressure>170 or h.minPressure<100
			or h.heartbeat>120 or h.heartbeat<45)
}

//No Bad health status with Good values
assert noBadHealthStatusWithGoodValues
{
	no h: HealthStatus | h.health=Bad
		and (h.maxPressure<=170 and h.minPressure>=100
			and h.heartbeat<=120 and h.heartbeat>=45)
}

//No run registration after registration deadline
assert noRegistrationAfterDeadline
{
	no r : RunRegistration, n : Run | r.registration=n
		and r.date>n.regDeadline
}

//No HealthstatusRecord without a device
assert noHealthStatusRecordWithoutDevice
{
	no h : HealthStatusRecord | no d : Device | h in d.records
}


//No Position Record without a smartphone
assert noPositionRecordWithoutSmartphone
{
	no p : PositionRecord | no s : Smartphone | p in s.records
}

//No Payment without data request
assert noPaymentWithoutDataRequest
{
	no p : Payment | no r : DataRequest | p in r.payment
}

//No smartphone without user
assert noSmartphoneWithoutUser
{
	no s : Smartphone | no u : StandardUser | s in u.smartphone
}

//No SOSCall without smartphone
assert noSOSCallWithoutSmartphone
{
	no c : SOSCall | no s : Smartphone | c in s.sosCall
}

//No device without smartphone
assert noDeviceWithoutSmartphone
{
	no d : Device | no s : Smartphone | d in s.device
}

//No position without Run or PositionRecord
assert noPositionWithoutRunOrPositionRecord
{
	no p : Position | no r : Run, pr : PositionRecord |
		p in r.route or p=pr.position
}

//No more than one registration for a run for the same user
assert noTwoRegSameUserSameRun
{
	no r1, r2 : RunRegistration | r1.registration=r2.registration
		and r1.runner=r2.runner and r1!=r2
}


run specialUsersCanMakeMoreThanOneDataRequest
run usersCanPartecipateInMoreThanOneRun
check noLessThan1000UsersInGroupDataRequests
check noPaymentForNotAcceptedSingleUserDataRequests
check noSOSCallWithoutBadStatus
check noGroupRequestsMoreThan1000UsersNotAccepted
check noSavedAddressesNotUsed
check noPaymentBeforeRequest
check noDownloadBeforeRequestAcceptedAndPaid
check noDeviceIsWorkingIfSmartphoneHasEmptyBattery
check noHealthStatusMaxPressureLowerThanMinPressure
check noGoodHealthStatusWithBadValues
check noBadHealthStatusWithGoodValues
check noRegistrationAfterDeadline
check noHealthStatusRecordWithoutDevice
check noPositionRecordWithoutSmartphone
check noPaymentWithoutDataRequest
check noSmartphoneWithoutUser
check noSOSCallWithoutSmartphone
check noDeviceWithoutSmartphone
check noPositionWithoutRunOrPositionRecord
check noTwoRegSameUserSameRun


pred show(){}

run show
