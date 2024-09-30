module projeto

// Definindo os horários possíveis
abstract sig Horario {}
one sig H8_10, H10_12, H14_16, H16_18 extends Horario {}  // 8h-10h, 10h-12h, 14h-16h, 16h-18h

// Definindo os dias úteis (segunda a sexta)
abstract sig Dia {}
one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

// Definindo os laboratórios (LCC1 e LCC2)
abstract sig Lab {}
one sig LCC1, LCC2 extends Lab {}

// Professor que faz reserva de aulas
sig Professor {
    disciplinas: set Disciplina
}

// Disciplina associada a um professor
sig Disciplina {
    horarios: set Horario
}

// Reserva de aulas
sig Aula {
    professor: one Professor,
    lab: one Lab,
    dia: some Dia,
    horario: some Horario
}

//////////////////
// FACTS //
//////////////////

fact MaximoDoisHorarios {
    all p: Professor | #p.disciplinas.horarios = 2
}

fact HorariosDiasAula {    
    all a: Aula | #a.dia = 2 and #a.horario = 2 and 
	 lone h1, h2: a.horario | h1 != h2 and h1.dia != h2.dia
}


run{}
