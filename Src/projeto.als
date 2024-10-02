module projeto

// Definindo os horários possíveis
abstract sig Horario {}
one sig H8_10, H10_12, H14_16, H16_18 extends Horario {}  // 8h-10h, 10h-12h, 14h-16h, 16h-18h

// Definindo os dias úteis (segunda a sexta)
abstract sig Dia {}
one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

// Definindo os laboratórios (LCC1 e LCC2)
abstract sig Lab {
    aulas: set Aula
}

one sig LCC1, LCC2 extends Lab {}

sig Pessoa {}

// Professor que faz reserva de aulas
sig Professor extends Pessoa{
	disciplinas: set Disciplina
}

sig Aluno extends Pessoa{}

// Disciplina associada a um professor
sig Disciplina {
    horarios: set Horario
}

// Reserva de aulas
sig Aula extends Atividade {
    professor: one Professor,
    dias: set Dia,
    disciplinas: set Disciplina
}

abstract sig Atividade {
	horarios: set Horario,
}

sig AtividadeExtra extends Atividade {
	pessoa: one Pessoa,
	dias: one Dia,
	lab: one Lab
}

// Reserva criada
sig Reserva {
	atividades: one Atividade
}

// Representaço da Lista de Espera
sig ListaEspera {
	reservas: set Reserva
}

// Predicado para verificar se uma atividade extra conflita com alguma aula em termos de horário
pred atividadeConflitanteComAula[ae: AtividadeExtra] {
    some a: Aula | 
        (a.dias & ae.dias) != none and 
        (a.horarios & ae.horarios) != none
}

// Restrição que coloca atividades extras na lista de espera se houver conflito de horários com aulas
fact AtividadeExtraEmListaDeEspera {
    all ae: AtividadeExtra |
        atividadeConflitanteComAula[ae] implies 
        some le: ListaEspera | ae in le.reservas.atividades
}


//Predicado para garantir que pessoa é um professor
pred ehProfessor[p: Pessoa]{
	p in Professor
}

// Predicado para garantir que a aula ocorra em um único laboratório
pred apenasEmUmLocal[a: Aula] {
    one l: Lab | a in l.aulas
}

// Predicado para garantir que aulas (sejam de professores diferentes ou iguais) não se sobreponham
pred aulasNaoSobrepostas[a1: Aula, a2: Aula] {
    a1 != a2 implies
    no (a1.dias & a2.dias) or no (a1.horarios & a2.horarios)
}

//////////////////
// FACTS //
//////////////////

//Garantir que toda disciplinas tem um professor
fact disciplinaTemProfessor {
    all d: Disciplina | one p: Professor | d in p.disciplinas
}


// Cada aula deve ter no máximo dois horários
fact MaximoDoisHorarios {
    all a: Aula | #a.horarios = 2
}


// Restrições sobre horários e dias
fact HorariosDiasAula {    
    all a: Aula | 
        #a.dias = 1 and 
        #a.horarios = 2
}

// Garantir que o horário da disciplina seja o mesmo da aula associada
fact HorarioDisciplinaAula {
    all a: Aula | 
        a.disciplinas.horarios = a.horarios
}

// Garantir que a disciplina esteja associada ao professor da aula
fact ProfessorDisciplinaAula {
    all a: Aula | 
        a.disciplinas in a.professor.disciplinas
}

// Restrições para garantir que uma disciplina só esteja associada a um único laboratório
fact DisciplinaUnicoLaboratorio {
    all d: Disciplina | 
        all a1, a2: Aula | d in a1.disciplinas and d in a2.disciplinas implies
        one l: Lab | a1 in l.aulas and a2 in l.aulas
}

fact disciplinaComUmProfessor{
	all d: Disciplina | one p: Pessoa | ehProfessor[p] implies(d in p.disciplinas)
}

// Garantir que cada disciplina tenha duas aulas
fact DisciplinaComDuasAulas {
    all d: Disciplina |
        # { a: Aula | d in a.disciplinas } = 2
}
/*
fact DisciplinaComUmProfessor {
    all d: Disciplina | 
        ( # { a: Aula | d in a.disciplinas } <= 1 ) implies 
        one p: Pessoa | ehProfessor[p] implies (d in p.disciplinas)
}
*/

fact DisciplinaComAulaSeProfessor {
    all p: Pessoa | 
        all d: Disciplina |
	   ehProfessor[p] implies
            (d in p.disciplinas implies 
            some a: Aula | d in a.disciplinas)
}

// Restrições de laboratório e sobreposição de aulas
fact {
    // Restrições de laboratório
    all disj l1, l2: Lab | 
        no (l1.aulas & l2.aulas)
    
    // Cada reserva deve estar associada a um único laboratório
    all a: Aula | apenasEmUmLocal[a]
    
    // Se a reserva for de um professor, deve cobrir dois horários
    all r: Aula | 
        r.professor = Professor implies 
        #(r.dias.horarios) = 2

    // Garantir que aulas não se sobreponham
    all a1, a2: Aula | 
        aulasNaoSobrepostas[a1, a2]
}

// Assert que garante que todas as aulas têm um professor associado
assert TodasAsAulasTemProfessor {
    all a: Aula | a.professor in Professor
}

// Assert que garante que uma disciplina sempre tem pelo menos uma aula associada, se um professor está associado a ela
assert DisciplinaTemAulaSeProfessor {
    all d: Disciplina | 
        d in Professor.disciplinas implies 
        some a: Aula | d in a.disciplinas
}

// Assert que garante que não há sobreposição de horários para aulas do mesmo professor
assert AulasDoMesmoProfessorNaoSobrepostas {
    all p: Pessoa, a1, a2: Aula | ehProfessor[p] implies
        (a1.professor = p and a2.professor = p implies
        aulasNaoSobrepostas[a1, a2])
}

// Assert que garante que cada disciplina só tem horários válidos
assert HorariosValidosDisciplina {
    all d: Disciplina | 
        d.horarios in Horario
}

run {} for exactly 2 Lab, 3 Pessoa, 5 Dia, 3 Disciplina, 3 Atividade, 2 Reserva, 1 ListaEspera
