module projeto

-----------------------------------------------------------------------------------------------------------
-- PROJETO:
-- Professor: Tiago Massoni

-- Caio Cesar Vieira Cavalcanti - 123110825
-- João Lucas Gomes Brandão - 123110397
-- João Pedro Azevedo do Nascimento - 123110768
-- Valdemar Victor Leite Carvalho - 123110796
-- Vinícius de Oliveira Porto - 123110505
-- Walber Wesley Félix de Araújo Filho - 123110522

-----------------------------------------------------------------------------------------------------------


-----------------------------------------------------------------------------------------------------------
-- ASSINATURAS
-----------------------------------------------------------------------------------------------------------

-- Definição abstrata de um horário.
abstract sig Horario {}

-- Horários específicos de 2 horas de duração.
one sig H8_10, H10_12, H14_16, H16_18 extends Horario {}

-- Definição abstrata de um dia.
abstract sig Dia {}

-- Dias da semana.
one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

-- Definição abstrata de um laboratório, que pode conter aulas.
abstract sig Lab {
    aulas: set Aula
}

-- Instâncias de laboratórios.
one sig LCC1, LCC2 extends Lab {}

-- Pessoa é uma entidade genérica, sem propriedades específicas.
sig Pessoa {}

-- Professor é uma especialização de Pessoa, associada a disciplinas.
sig Professor extends Pessoa {
    disciplinas: set Disciplina
}

-- Aluno também é uma especialização de Pessoa.
sig Aluno extends Pessoa {}

-- Disciplina tem horários e alunos associados.
sig Disciplina {
    horarios: set Horario,
    alunos: set Aluno
}

-- Atividade é uma entidade abstrata, com horários e um dia definidos.
abstract sig Atividade {
    horarios: set Horario,
    dia: one Dia
}

-- Aula é uma especialização de Atividade, associada a um professor e uma disciplina.
sig Aula extends Atividade {
    professor: one Professor,
    disciplinas: set Disciplina,
} {
    #disciplinas = 1 -- Uma aula só pode ter uma disciplina.
}

-- AtividadeExtra é uma especialização de Atividade, vinculada a uma pessoa e a um laboratório.
sig AtividadeExtra extends Atividade {
    pessoa: one Pessoa, 
    lab: one Lab
} {
    #horarios = 1 -- AtividadeExtra só pode ter um horário.
}

-- Reserva está associada a uma única atividade.
sig Reserva {
    atividades: one Atividade
}

-- Lista de espera contém reservas.
one sig ListaEspera {
    reservas: set Reserva
}

-----------------------------------------------------------------------------------------------------------
-- PREDICADOS
-----------------------------------------------------------------------------------------------------------

-- Verifica se uma AtividadeExtra entra em conflito com uma Aula.
pred atividadeConflitanteComAula[ae: AtividadeExtra] {
    some a: Aula | 
        (a.dia = ae.dia) and 
        (a.horarios & ae.horarios) != none and
        aEmLaboratorio[a, ae.lab]
}

-- Verifica se uma aula ocorre em um laboratório específico.
pred aEmLaboratorio[a: Aula, l: Lab] {
    a in l.aulas
}

-- Verifica se uma pessoa é professor.
pred ehProfessor[p: Pessoa] {
    p in Professor
}

-- Verifica se uma aula está em apenas um laboratório.
pred apenasEmUmLocal[a: Aula] {
    one l: Lab | a in l.aulas
}

-- Verifica se duas aulas não têm sobreposição de horários e dias.
pred aulasNaoSobrepostas[a1: Aula, a2: Aula] {
    a1 != a2 implies
    (a1.dia != a2.dia) and (a1.horarios & a2.horarios = none)
}

-- Verifica se não há choque entre duas atividades na lista de espera.
pred verificarAtividadeListaEspera[atv1, atv2: Atividade, le: ListaEspera] {
    atv1 != atv2 and
    atv1.horarios = atv2.horarios and
    atv1.dia = atv2.dia and
    (atv1 in Aula implies atv2 in Aula implies (aEmLaboratorio[atv1, atv2.lab])) 
    implies
    atv2 in le.reservas.atividades
}

-- Garante que não há duas reservas para a mesma atividade.
pred reservasUnicasPorAtividade {
    all disj r1, r2: Reserva | r1.atividades != r2.atividades
}

-----------------------------------------------------------------------------------------------------------
-- FATOS
-----------------------------------------------------------------------------------------------------------

-- Garante que toda disciplina tem um professor.
fact disciplinaTemProfessor {
    all d: Disciplina | one p: Professor | d in p.disciplinas
}

-- Garante que toda aula tem exatamente dois horários.
fact MaximoDoisHorarios {
    all a: Aula | #a.horarios = 1
}

-- Garante que toda aula tem um único dia e um único horário por vez.
fact HorariosDiasAula {    
    all a: Aula | 
        #a.dia = 1 and 
        #a.horarios = 1
}

-- Garante que os horários da disciplina coincidem com os horários da aula.
fact HorarioDisciplinaAula {
    all a: Aula | 
        a.disciplinas.horarios = a.horarios
}

-- Garante que o professor da aula é responsável pela disciplina.
fact ProfessorDisciplinaAula {
    all a: Aula | 
        a.disciplinas in a.professor.disciplinas
}

-- Garante que uma disciplina só pode ser alocada em um único laboratório.
fact DisciplinaUnicoLaboratorio {
    all d: Disciplina | 
        all a1, a2: Aula | d in a1.disciplinas and d in a2.disciplinas implies
        one l: Lab | a1 in l.aulas and a2 in l.aulas
}

-- Garante que toda disciplina tem exatamente um professor.
fact disciplinaComUmProfessor {
    all d: Disciplina | one p: Pessoa | ehProfessor[p] implies (d in p.disciplinas)
}

-- Garante que cada disciplina tem duas aulas.
fact DisciplinaComDuasAulas {
    all d: Disciplina |
        # { a: Aula | d in a.disciplinas } = 2
}

-- Garante que toda disciplina tem uma aula se for associada a um professor.
fact DisciplinaComAulaSeProfessor {
    all p: Pessoa | 
    all d: Disciplina |
        ehProfessor[p] implies
            (d in p.disciplinas implies 
            some a: Aula | d in a.disciplinas)
}

-- Fato que previne aulas duplicadas em diferentes laboratórios e garante que as aulas não estão sobrepostas.
fact {
    all disj l1, l2: Lab | 
        no (l1.aulas & l2.aulas)
    
    all a: Aula | apenasEmUmLocal[a]
    
    all a1, a2: Aula | 
        aulasNaoSobrepostas[a1, a2]
}

-- Garante que reservas para atividades são únicas.
fact UnicidadeDeAtividadesNasReservas {
    reservasUnicasPorAtividade
}

-- Garante que toda atividade está associada a uma reserva ou está na lista de espera.
fact AtividadeAssociadaAReservaOuListaEspera {
    all a: Atividade | 
        (some r: Reserva | r.atividades = a) or
        (some le: ListaEspera | a in le.reservas.atividades)
}

-- Verifica e trata os conflitos de reserva, colocando atividades em espera quando necessário.
fact ConflitoDeReservaEListaEspera {
    all disj atv1, atv2: Atividade | 
        atv1.horarios = atv2.horarios and
        atv1.dia = atv2.dia and
        (
            (atv1 in Aula and atv2 in Aula and 
            some l: Lab | aEmLaboratorio[atv1, l] and aEmLaboratorio[atv2, l]) 
            or 
            (atv1 in Aula and atv2 in AtividadeExtra and aEmLaboratorio[atv1, atv2.lab]) 
        ) implies {
            (atv1 in Aula and atv2 in AtividadeExtra) implies atv2 in ListaEspera.reservas.atividades
            (atv1 in Aula and atv2 in Aula) implies 
            (atv1 in ListaEspera.reservas.atividades or atv2 in ListaEspera.reservas.atividades)
        }
}

-----------------------------------------------------------------------------------------------------------
-- ASSERTS
-----------------------------------------------------------------------------------------------------------

-- Verifica se toda aula tem um professor.
assert TodasAsAulasTemProfessor {
    all a: Aula | a.professor in Professor
}

-- Garante que disciplinas com professores têm aulas.
assert DisciplinaTemAulaSeProfessor {
    all d: Disciplina | 
        d in Professor.disciplinas implies 
        some a: Aula | d in a.disciplinas
}

-- Garante que aulas do mesmo professor não estão sobrepostas.
assert AulasDoMesmoProfessorNaoSobrepostas {
    all p: Pessoa, a1, a2: Aula | ehProfessor[p] implies
        (a1.professor = p and a2.professor = p implies
        aulasNaoSobrepostas[a1, a2])
}

-- Garante que todos os horários de cada disciplina são válidos e pertencem à assinatura Horario.
assert HorariosValidosDisciplina {
    all d: Disciplina | 
        d.horarios in Horario
}

-- Verifica que, se uma aula e uma atividade extra ocorrem no mesmo dia e compartilham horários,
-- então a atividade extra deve estar na lista de espera, e a aula não deve estar entre as reservas da lista.
assert AulaNaoReservadaComAtividadeExtraNaListaDeEspera {
    all a: Aula, ae: AtividadeExtra, le: ListaEspera |
        (a.dia = ae.dia) implies
        (a.horarios & ae.horarios) != none and
        aEmLaboratorio[a, ae.lab] and
        ae in le.reservas implies
        a !in le.reservas.atividades
}

-- Garante que, se duas aulas ocorrem no mesmo dia e têm horários sobrepostos,
-- então se uma delas não está no laboratório, a outra deve estar nele.
assert ReservaEmLabDisponivel {
    all a1: Aula, a2: Aula, l: Lab |
        a1 != a2 and
        (a1.dia = a2.dia) and
        (a1.horarios & a2.horarios) != none implies
        (a1 !in l.aulas implies a2 in l.aulas)
}

-- Verifica que, se duas aulas estão alocadas no mesmo laboratório,
-- elas devem ocorrer no mesmo dia e ter horários que se sobrepõem.
assert ReservaUnicoLab {
    all a1, a2: Aula |
        a1.lab = a2.lab implies
        (a1.dia = a2.dia and
        (a1.horarios & a2.horarios) != none)
}

-- Assegura que cada AtividadeExtra tem exatamente um horário associado.
assert AtividadeExtraComUmHorario {
    all ae: AtividadeExtra | 
        #ae.horarios = 1
}

-- Garante que cada aula está associada a exatamente uma disciplina.
assert AulaComDisciplinasUnicas {
    all a: Aula | 
        #a.disciplinas = 1
}

-- Verifica que cada reserva está associada a uma atividade, que pode ser uma aula ou uma atividade extra.
assert ReservaAssociadaAtividade {
    all r: Reserva | r.atividades in Aula or r.atividades in AtividadeExtra
}

-- Assegura que não existem duas reservas para a mesma atividade, garantindo a unicidade.
assert UnicidadeDeReservasPorAtividade {

    all disj r1, r2: Reserva | r1.atividades != r2.atividades
}

-- Garante que, se uma reserva está associada a uma aula, não deve haver sobreposição de horários com outra aula.
assert AulasNaoSobrepostasComReservas {
    all a: Aula, r: Reserva | 
        r.atividades in Aula implies
        (r.atividades.horarios & a.horarios = none) or
        (a !in r.atividades)
}

-- Verifica que toda atividade deve ter pelo menos uma reserva ou deve estar na lista de espera.
assert AtividadeComUmaReservaOuListaEspera {
    all a: Atividade | 
        (some r: Reserva | r.atividades = a) or
        (some le: ListaEspera | a in le.reservas.atividades)
}

-- Teste para garantir que um professor não tenha duas disciplinas com horários sobrepostos.
assert TesteProfcom2DiscSobrepostas { 
    all p: Professor | 
        no r1, r2: Reserva | 
        r1.atividades.professor = p and r2.atividades.professor = p and 
        r1.atividades != r2.atividades and 
        r1.horarios = r2.horarios
}

-- Teste para garantir que as reservas só podem ser feitas com duração de duas horas por dia.
assert TesteReservasDuasHoras {
    all r: Reserva |
        #r.atividades.horarios = 1
}

-- Teste para garantir que cada reserva deve ter um horário, um laboratório e uma atividade associada.
assert TesteReservaCompleta {
    all r: Reserva | 
        some r.atividades and 
        some l: Lab | r.atividades in Aula or r.atividades in AtividadeExtra
}

-- Teste para garantir que uma disciplina está alocada em apenas um laboratório.
assert TesteMesmaDisciplinaMesmoLaboratorio {
    all d: Disciplina | 
        let reservas = {r: Reserva | d in r.atividades.disciplinas} |
        #reservas = 2 => 
            all r1, r2: reservas | r1.atividades.lab = r2.atividades.lab
}

-- Teste para garantir que não há sobreposição de laboratórios para aulas com o mesmo professor.
assert SobreposicaoReservas {
    all r1, r2: Reserva | 
        r1.atividades in Aula and r2.atividades in Aula and
        r1.atividades.professor = r2.atividades.professor and 
        r1.atividades.horarios = r2.atividades.horarios => r1 = r2
}

-- Teste para garantir que se há uma disciplina na lista de espera de um horário,
-- não haverá uma atividade extra usando o laboratório no mesmo horário.
assert TesteListaEsperaDisciplinaSemConflito {
    all le: ListaEspera | 
        all r: Reserva | r in le.reservas implies 
            all d: Disciplina | d in r.atividades.disciplinas implies 
                no r2: Reserva | 
                    r2.atividades in AtividadeExtra and 
                    r2.atividades.lab = r.atividades.lab and 
                    r2.atividades.horarios = r.atividades.horarios
}

-- Teste para garantir que uma disciplina não estará simultaneamente reservada e na lista de espera.
assert TesteNumReservasDisciplinas {
    all d: Disciplina |
        let reservaD = {r: Reserva | d in r.atividades.disciplinas},
            filaD = {le: ListaEspera | d in le.reservas.atividades} |
        (#reservaD = 2 and #filaD = 0) or (#reservaD = 0 and #filaD = 2)
}

-- Teste para garantir que cada professor não poderá reservar o mesmo horário mais de uma vez.
assert TesteUmaReservaProfessorPorHorario {
    all p: Professor | 
        all r1, r2: Reserva | 
        r1.atividades in Aula and r2.atividades in Aula and
        r1.atividades.professor = p and r2.atividades.professor = p and
        r1 != r2 => r1.horarios != r2.horarios
}

-- Teste para garantir que uma atividade que já está reservada não poderá estar na fila de espera.
assert TesteAtivReservadaListaEspera {
    all r: Reserva | 
        r.atividades in Aula implies 
        no le: ListaEspera | r.atividades in le.reservas.atividades
}

-- Teste para garantir que um professor não pode alocar um laboratório para uma atividade extra se já estiver alocado uma disciplina no mesmo horário.
assert TesteProfessorDisciplinaAtividadeExtra {
    all p: Professor |
        all r1: Reserva | 
            r1.atividades in Aula and r1.atividades.professor = p =>
                no r2: Reserva |
                    r2.atividades in AtividadeExtra and r2.horarios = r1.horarios and r2.atividades.professor = p
}

-- Teste para garantir que todas as disciplinas tenham pelo menos um aluno associado a elas.
assert TesteDisciplinaComAlunos { 
    all d: Disciplina | 
        some a: Aluno | a in d.alunos
}

-- Teste para garantir que cada disciplina tenha exatamente um professor.
assert TesteUmProfessorPorDisciplina {
    no d: Disciplina | #d.professor != 1 
}

-- Teste para garantir que uma atividade não ocupa mais que uma vaga na fila de espera.
assert TesteNumFilaAtv {
    all a: AtividadeExtra |
        let filas = {r: Reserva | a in r.atividades} |
        #filas <= 1
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

check ReservaAssociadaAtividadeCheck {
    all r: Reserva | r.atividades in Aula or r.atividades in AtividadeExtra
}

check UnicidadeDeReservasPorAtividadeCheck {
    all disj r1, r2: Reserva | r1.atividades != r2.atividades
}

check AulasNaoSobrepostasComReservasCheck {
    all a: Aula, r: Reserva | 
        r.atividades in Aula implies
        (r.atividades.horarios & a.horarios = none)
}

check AtividadeComUmaReservaOuListaEsperaCheck {
    all a: Atividade | 
        (some r: Reserva | r.atividades = a) or
        (some le: ListaEspera | a in le.reservas.atividades)
}

check TesteReservaCompleta for 30

check SobreposicaoReservas for 30

check TesteMesmaDisciplinaMesmoLaboratorio for 30

check TesteReservasDuasHoras for 30

check TesteNumReservasDisciplinas for 30

check TesteUmaReservaProfessorPorHorario for 30

check TesteAtivReservadaListaEspera for 30

check TesteProfessorDisciplinaAtividadeExtra for 30

check TesteProfcom2DiscSobrepostas for 30

check TesteDisciplinaComAlunos for 30

check TesteUmProfessorPorDisciplina for 30

check TesteNumFilaAtv for 30


run {}
