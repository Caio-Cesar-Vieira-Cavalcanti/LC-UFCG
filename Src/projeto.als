module projeto

-----------------------------------------------------------------------------------------------------------
-- ASSINATURAS
-----------------------------------------------------------------------------------------------------------

abstract sig Horario {}

one sig H8_10, H10_12, H14_16, H16_18 extends Horario {}

abstract sig Dia {}

one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

abstract sig Lab {
    aulas: set Aula
}

one sig LCC1, LCC2 extends Lab {}

sig Pessoa {}

sig Professor extends Pessoa {
    disciplinas: set Disciplina
}

sig Aluno extends Pessoa {}

sig Disciplina {
    horarios: set Horario
}

abstract sig Atividade {
    horarios: set Horario,
}

sig Aula extends Atividade {
    professor: one Professor,
    dia: one Dia,
    disciplinas: set Disciplina,
} {
    #disciplinas = 1
}

sig AtividadeExtra extends Atividade {
    pessoa: one Pessoa,
    dia: one Dia, 
    lab: one Lab
} {
    #horarios = 1
}

sig Reserva {
    atividades: one Atividade
}

sig ListaEspera {
    reservas: set Reserva
}

-----------------------------------------------------------------------------------------------------------
-- PREDICADOS
-----------------------------------------------------------------------------------------------------------

pred atividadeConflitanteComAula[ae: AtividadeExtra] {
    some a: Aula | 
        (a.dia = ae.dia) and 
        (a.horarios & ae.horarios) != none and
        aEmLaboratorio[a, ae.lab]
}

pred aEmLaboratorio[a: Aula, l: Lab] {
    a in l.aulas
}

pred ehProfessor[p: Pessoa] {
    p in Professor
}

pred apenasEmUmLocal[a: Aula] {
    one l: Lab | a in l.aulas
}

pred aulasNaoSobrepostas[a1: Aula, a2: Aula] {
    a1 != a2 implies
    (a1.dia != a2.dia) and (a1.horarios & a2.horarios = none)
}

-----------------------------------------------------------------------------------------------------------
-- FATOS
-----------------------------------------------------------------------------------------------------------

fact disciplinaTemProfessor {
    all d: Disciplina | one p: Professor | d in p.disciplinas
}

fact MaximoDoisHorarios {
    all a: Aula | #a.horarios = 2
}

fact HorariosDiasAula {    
    all a: Aula | 
        #a.dia = 1 and 
        #a.horarios = 1
}


fact HorarioDisciplinaAula {
    all a: Aula | 
        a.disciplinas.horarios = a.horarios
}

fact ProfessorDisciplinaAula {
    all a: Aula | 
        a.disciplinas in a.professor.disciplinas
}

fact DisciplinaUnicoLaboratorio {
    all d: Disciplina | 
        all a1, a2: Aula | d in a1.disciplinas and d in a2.disciplinas implies
        one l: Lab | a1 in l.aulas and a2 in l.aulas
}

fact disciplinaComUmProfessor {
    all d: Disciplina | one p: Pessoa | ehProfessor[p] implies (d in p.disciplinas)
}

fact DisciplinaComDuasAulas {
    all d: Disciplina |
        # { a: Aula | d in a.disciplinas } = 2
}

fact DisciplinaComAulaSeProfessor {
    all p: Pessoa | 
    all d: Disciplina |
        ehProfessor[p] implies
            (d in p.disciplinas implies 
            some a: Aula | d in a.disciplinas)
}

fact {
    all disj l1, l2: Lab | 
        no (l1.aulas & l2.aulas)
    
    all a: Aula | apenasEmUmLocal[a]
    
    all a1, a2: Aula | 
        aulasNaoSobrepostas[a1, a2]
}

-----------------------------------------------------------------------------------------------------------
-- ASSERTS
-----------------------------------------------------------------------------------------------------------

assert TodasAsAulasTemProfessor {
    all a: Aula | a.professor in Professor
}

assert DisciplinaTemAulaSeProfessor {
    all d: Disciplina | 
        d in Professor.disciplinas implies 
        some a: Aula | d in a.disciplinas
}

assert AulasDoMesmoProfessorNaoSobrepostas {
    all p: Pessoa, a1, a2: Aula | ehProfessor[p] implies
        (a1.professor = p and a2.professor = p implies
        aulasNaoSobrepostas[a1, a2])
}

assert HorariosValidosDisciplina {
    all d: Disciplina | 
        d.horarios in Horario
}

assert AulaNaoReservadaComAtividadeExtraNaListaDeEspera {
    all a: Aula, ae: AtividadeExtra, le: ListaEspera |
        (a.dia = ae.dia) implies
        (a.horarios & ae.horarios) != none and
        aEmLaboratorio[a, ae.lab] and
        ae in le.reservas implies
        a !in le.reservas.atividades
}

assert ReservaEmLabDisponivel {
    all a1: Aula, a2: Aula, l: Lab |
        a1 != a2 and
        (a1.dia = a2.dia) and
        (a1.horarios & a2.horarios) != none implies
        (a1 !in l.aulas implies a2 in l.aulas)
}

assert ReservaUnicoLab {
    all a1, a2: Aula |
        a1.lab = a2.lab implies
        (a1.dia = a2.dia and
        (a1.horarios & a2.horarios) != none)
}

assert AtividadeExtraComUmHorario {
    all ae: AtividadeExtra | 
        #ae.horarios = 1
}

assert AulaComDisciplinasUnicas {
    all a: Aula | 
        #a.disciplinas = 1
}

-----------------------------------------------------------------------------------------------------------
-- TESTES
-----------------------------------------------------------------------------------------------------------

check ReservaEmLabDisponivelCheck {
    all a1: Aula, a2: Aula, l: Lab |
        a1 != a2 and
        (a1.dia = a2.dia) and
        (a1.horarios & a2.horarios) != none implies
        (a1 !in l.aulas implies a2 in l.aulas)
}

check AulasDoMesmoProfessorNaoSobrepostasCheck {
    all p: Pessoa, a1, a2: Aula | ehProfessor[p] implies
        (a1.professor = p and a2.professor = p implies
        aulasNaoSobrepostas[a1, a2])
}

check HorariosValidosDisciplinaCheck {
    all d: Disciplina | 
        d.horarios in Horario
}

check ReservaUnicoLabCheck {
    all a1, a2: Aula |
        a1.lab = a2.lab implies
        (a1.dia = a2.dia and
        (a1.horarios & a2.horarios) != none)
}


check AulaComUmHorarioCheck {

    all a: Aula | #a.horarios = 1

}


check AulaNaoReservadaComAtividadeExtraNaListaDeEsperaCheck {

    all a: Aula, ae: AtividadeExtra, le: ListaEspera |

        (a.dia & ae.dia) != none and

        (a.horarios & ae.horarios) != none and

        aEmLaboratorio[a, ae.lab] implies

        a !in le.reservas.atividades

}

check DisciplinaTemAulaSeProfessorCheck {
    all p: Pessoa, d: Disciplina |
        ehProfessor[p] implies
            (d in p.disciplinas implies some a: Aula | d in a.disciplinas)
}

run {
	#Reserva > 1

} for 8
