module projeto

/*
PRIMEIRA VERSÃO
*/

// Definindo os horários possíveis
abstract sig Horario {}
one sig H8_10, H10_12, H14_16, H16_18 extends Horario {} // 8h-10h, 10h-12h, 14h-16h, 16h-18h

// Definindo os dias úteis (segunda a sexta)
abstract sig Dia {}
one sig Segunda, Terca, Quarta, Quinta, Sexta extends Dia {}

// Definindo os laboratórios (LCC1 e LCC2)
abstract sig Lab {}
one sig LCC1, LCC2 extends Lab {}

// Professor que faz reserva com disciplina associada
sig Professor {
    disciplinas: set Disciplina
}

// Disciplina associada a um professor
sig Disciplina {
    horarios: set Horario
}

// Reserva de laboratórios
sig Reserva {
    professor: one Professor,
    lab: one Lab,
    dia: one Dia,
    horario: one Horario
}

// Lista de espera por laboratório e horário
sig Espera {
    professor: one Professor,
    dia: one Dia,
    horario: one Horario,
    lab: one Lab
}

// Regras (Facts)

// Professores podem reservar no máximo dois horários semanais para suas disciplinas
fact MaximoDoisHorarios {
    all p: Professor | #p.disciplinas.horarios <= 2
}

// Uma reserva só pode ser feita se o horário e o laboratório estiverem disponíveis
fact ReservasValidas {
    all r: Reserva | 
        no r2: Reserva | 
        (r.lab = r2.lab and r.dia = r2.dia and r.horario = r2.horario and r != r2)
}

// Um horário de disciplina não pode coincidir com um horário da lista de espera enquanto houver reserva de horário sem disciplina
fact ListaEsperaRestricao {
    all e: Espera | 
        all r: Reserva | 
        (e.horario = r.horario and e.dia = r.dia and e.lab = r.lab) 
        implies some r.professor.disciplinas
}

// Um pedido da lista de espera pode ser contemplado em outro laboratório se houver horário disponível
fact ListaEsperaTransferencia {
    all e: Espera | 
        no r1: Reserva | (r1.dia = e.dia and r1.horario = e.horario and r1.lab = LCC1) 
        implies no r2: Reserva | (r2.dia = e.dia and r2.horario = e.horario and r2.lab = LCC2)
}

// Asserts

// Garante que nenhum professor tem mais de dois horários reservados
assert VerificaLimiteHorarios {
    all p: Professor | #p.disciplinas.horarios <= 2
}

// Verifica se não há conflitos de reservas (mais de uma reserva no mesmo horário e laboratório)
assert VerificaConflitosReservas {
    all r: Reserva | 
        no r2: Reserva | 
        (r.lab = r2.lab and r.dia = r2.dia and r.horario = r2.horario and r != r2)
}

// Verifica se a lista de espera respeita a regra de disciplina associada
assert VerificaEsperaDisciplina {
    all e: Espera | 
        all r: Reserva | 
        (e.horario = r.horario and e.dia = r.dia and e.lab = r.lab) 
        implies some r.professor.disciplinas
}

// Comandos para checar os asserts

check VerificaLimiteHorarios for 5 but exactly 3 Reserva, exactly 5 Professor, exactly 5 Dia, exactly 4 Horario, exactly 2 Lab
check VerificaConflitosReservas for 5 but exactly 3 Reserva, exactly 5 Professor, exactly 5 Dia, exactly 4 Horario, exactly 2 Lab
check VerificaEsperaDisciplina for 5 but exactly 3 Reserva, exactly 5 Professor, exactly 5 Dia, exactly 4 Horario, exactly 2 Lab