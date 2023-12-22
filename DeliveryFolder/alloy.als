// Signatures

// Useful for defining all the attributes of a user
abstract sig User {
	id: one Int,
	name: one String, 
	lastname: one String,
	email: one String
}

//Profile of a Student
sig Profile{ 
	badgesCollected: set Badge
}

//Definition of a Student
sig Student extends User {
	profile: one Profile, 
	notificationsNotYetRead: set Notification
}

//Definition of an Educator, concretized in Admin and Collaborator
abstract sig Educator extends User {
}

//Definition of an Admin, who is the creator of a Tournament
sig Admin extends Educator{
	tournamentsCreated: set Tournament 
}

//Definition of a Collaborator, who can collaborate in tournaments
sig Collaborator extends Educator{
	PartecipatingTournaments: set Tournament
}

// Definition of a Variable, useful for defining new rules
sig Variable {
	name: one String
}

//Definition of a Rule, useful for defining new badges
sig Rule {
	name: one String,
	variables: some Variable
}

//Definition of a Badge, which are created by educators and can be assigned to students
sig Badge {
	title: one String,
	rules: some Rule	
} 

//Boolean useful to modelize the status of tournaments and battles (open or closed)
abstract sig Bool {}
one sig TRUE extends Bool {}
one sig FALSE extends Bool {}

// Simplified model of a date, managed with integers
sig Date{
	date: one Int
}{ date >= 0 }

//maxScore can be different from battle to battle, to allow Educators 
//decide for an optional manual evaluation
sig Score {
    value: one Int
} {
    value >= 0  and value <= Battle.maxScore
}

//Definition of the programming Language 
sig ProgrammingLanguage {}

//Definition of a Tournament
sig Tournament {
	id: one Int,
	name: one String,
	registrationDeadline: one Date,
	endOfTournament: one Date,
	rankingOfStudents: set Student, 
	battles: set Battle,
	programmingLanguage: one ProgrammingLanguage,
	isOpen: one Bool,
	badgesCreated: set Badge
}{
	//Integrity constraint on dates
	registrationDeadline.date > 0
	registrationDeadline.date < endOfTournament.date
	
	all b: Battle | b in battles implies registrationDeadline.date < b.registrationDeadline.date 
		and b.endOfBattle.date <= endOfTournament.date
	
}

//Definition of a Battle
sig Battle {
	id: one Int,
	name: one String,
	registrationDeadline: one Date,
	endOfBattle: one Date,
	rankingOfTeams: set Team, 
	teams: set Team,
	isOpen: one Bool,
	maxScore: one Int,
	maxTeamMembers: one Int,
	minTeamMembers: one Int,
	codekata: one CodeKata 
}{
	// Constraints on some attributes
	minTeamMembers <= maxTeamMembers and minTeamMembers > 0 
	registrationDeadline.date < endOfBattle.date
	maxScore > 0 

	// Ensure that rankingOfTeams is the same as the set of teams in the battle
	rankingOfTeams = teams

	// Ensure that codekata in a battle is the same as codekata in a repo,
	// if the repo belongs to a team in that battle
	all t: teams | codekata = t.repo.codekata
}

//Definition of a Team
sig Team {
	id: one Int,
	name: one String,
	members: some Student, 
	score: one Score,
	repo: one Repo
}

//Definition of a Repo, to manage the association with the GitHub repository
sig Repo{
	codekata: one CodeKata
}

//Definition of a CodeKata
sig CodeKata{
	programmingLanguage: one ProgrammingLanguage,
	description: one String,
	softwareProject: one SoftwareProject
}

//Definition of Software Project, which includes test cases and build automation scripts
sig SoftwareProject{
	tests: some Test
}

//Definition of a test
sig Test{}

//The Notification Center is responsible to manage the notification mechanism
one sig NotificationCenter{} 

//Definition of a Notification
sig Notification { 
	message: one String
}


// Facts and Constraints

// Constraint to ensure that if isOpen of a Battle in a Tournament is TRUE,
// then isOpen of the corresponding Tournament can't be FALSE
fact consistentBattleTournamentStatus{
	all t: Tournament, b: t.battles |
		b.isOpen = TRUE implies t.isOpen = TRUE
}

// Constraint to ensure that rankingOfTeams has only teams that belong to the set teams of the battle
fact validRankingOfTeams {
    all b: Battle | b.rankingOfTeams in b.teams
}

 // Constraint to ensure that the profile of a Student is always different
fact differentProfilesOfStudents{
    all s1, s2: Student | s1 != s2 implies s1.profile != s2.profile
}

// Fact to ensure uniqueness of IDs
fact uniqueIDs {
	all disj u1, u2: User | u1.id != u2.id
	all disj t1, t2: Tournament | t1.id != t2.id
	all disj b1, b2: Battle | b1.id != b2.id 
	all disj tm1, tm2: Team | tm1.id != tm2.id
}

// Fact to ensure positive IDs
fact positiveID{
	all u: User | u.id >= 0
	all t: Tournament | t.id >= 0
	all b: Battle | b.id >= 0
	all t: Team | t.id >= 0	
}

// Fact to ensure unique Team names in a Battle and other name constraints
fact uniqueNames {
	all b: Battle | all disj tm1, tm2: b.teams | tm1.name != tm2.name 
	all t: Tournament | all disj b1, b2: t.battles | b1.name != b2.name 
	all disj t1, t2: Tournament | t1.name != t2.name
}

// To guarantee different teams in the same Battle
fact DifferentTeamMembersInABattle {
    all b: Battle | all t1, t2: b.teams | t1 != t2 implies no t1.members & t2.members
}

// To guarantee different battles in Tournaments
fact DifferentBattlesInTournaments {
    all disj t1, t2: Tournament | no t1.battles & t2.battles
}

// Teams have different Repo
fact DifferentRepoForTeams{
	all disj tm1,tm2: Team, r1: tm1.repo, r2: tm2.repo | r1 != r2
}

//Battle have different teams
fact DifferentTeamInDifferentBattle{
	all disj b1, b2: Battle,  tm1: b1.teams, tm2: b2.teams | tm1!=tm2
}

// Constraint to ensure that each Battle belongs to a Tournament
fact battleBelongsToTournament {
	all b: Battle | one t: Tournament | b in t.battles
}

// Constraint to ensure that each Team belongs to a Battle
fact teamBelongsToBattle {
	all t: Team | one b: Battle | t in b.teams
}

// Constraint to ensure that profiles are always different from student to student
fact differentProfilesOfStudents {
    all s1, s2: Student | s1 != s2 implies s1.profile != s2.profile
}

// Ensures that every Profile belongs to a Student
fact everyProfileBelongsToStudent {
    all p: Profile | one s: Student | s.profile = p
}

//Ensures that every CodeKata has his own Software Project
fact differentSoftwareProjectsOfCodeKata{
	all c1, c2: CodeKata | c1 != c2 implies c1.softwareProject != c2.softwareProject
}

// Constraint to ensure that each sig Test belongs to a CodeKata
fact testBelongsToSoftwareProject {
	all t: Test | one sw: SoftwareProject | t in sw.tests
}

// Constraint to ensure that for all Tournaments there exists exactly one Admin
fact adminAndCollaboratorsForTournaments {
    all t: Tournament |
        one a: Admin | t in a.tournamentsCreated 
}

// To manage strings in alloy, simplified model of a String
fact stringPool {
    none != "a" + "b" + "c" + "d" + "e" 
}


// Constraint to ensure that programmingLanguage in CodeKata must be the same of
// programmingLanguage in a Tournament (if the CodeKata belongs to a repo of a Team
// inside the Tournament)
fact consistentProgrammingLanguage {
    all t: Tournament, b: t.battles, tm: b.teams, r: tm.repo, ck: r.codekata |
        ck.programmingLanguage = t.programmingLanguage
}

// Constraint to ensure that for every Tournament there is at least one Badge created
fact atLeastOneBadgePerTournament {
    all t: Tournament |
        some b: Badge | b in t.badgesCreated
}

// Constraint to ensure that if a Tournament is closed, a badge can be assigned to some students
// (In a profile of a Student can also exist other badges he may have collected)
fact badgeAssignedAtTheEndOfTournament {
    all t: Tournament, b: t.battles, tm: b.teams, s: tm.members, p: s.profile, bd: p.badgesCollected |
        t.isOpen = FALSE iff bd in t.badgesCreated
}

// Example
pred show []{
	#Tournament = 2
	#Educator > 1
	#Team = 2
}

run show for 3
