
----------------------------------------SIGNATURES-------------------------------------------------
sig Player{
	favorites: set Serie
}

sig Serie{
	season: set Season
}

sig Season{
	quiz :  one Quiz
}

sig Quiz{
	questoes: set Question
}

sig Question{
	level: Level
}
abstract sig Level{}

one sig EASY,HARD extends Level{}


--------------------------------------------FACTS-----------------------------------------------------
fact Player{
	
	// o usuario pode ter ou não series favoritas
	all p: Player | #getFavorites[p] = 0 or #getFavorites[p] > 1

}

fact QuestionEQuiz{

	// a questao só pode ter um level
	all qe: Question | #getLevelQuestion[qe] = 1

	// quiz só pode ter um season
	all qi:Quiz  |  lone qi.~quiz

	// os quizes tem que ter mais de 0 questoes e menos que 11
	all qi:Quiz |( #qi.questoes > 0 and #qi.questoes < 11)
	
	//cada questao só pode estar em um quiz
	all qe:Question | #qe.~questoes = 1
}

fact Serie{
	//a serie pode ter muitas temporadas
	all s:Serie | #getSeason[s] >= 1
	
}

fact Season{
	all s:Season | #s.~season = 1
}

----------------------------------------FUNCTIONS--------------------------------------------------
fun getFavorites[p:Player] : set Serie{	
	p.favorites
}

fun getLevelQuestion[qe:Question] : set Level{
	qe.level
}

fun getSeason[s:Serie]: set Season{
	s.season
}

pred show[]{
}


--------------------------------------------ASSERTS----------------------------------------------------

assert assertPlayer{
	all p : Player | #(p.favorites) > -1
}

assert assertSerie {
	all serie : Serie | #(serie.season) > 0
}

assert assertSeason{
	all season : Season | #(season.quiz) = 1
}

assert assertQuiz{
	all quiz : Quiz | #(quiz.questoes) > -1 and #(quiz.questoes) < 11
}



run show for 10 but exactly 1 Player, exactly 5 Serie, exactly 10 Season, exactly 10 Quiz, exactly 10 Question


check assertPlayer for 13

check assertSerie for 13

check assertSeason for 13

check assertQuiz for 13
