module projeto

abstract sig Lab {}
abstract sig Dia {}
abstract sig Hora {}

one sig Lcc1, Lcc2 extends Lab {}
one sig Seg, Ter, Qua, Qui, Sex extends Dia {}
one sig H8_10, H10_12, H14_16, H16_18 extends Hora {}

sig Horario {
    dia: Dia,
    hora: Hora,
    filaDeEspera: set Atividade,
}

abstract sig Reserva {
    horario: Horario,
    lab: Lab,
    atividade: Atividade,
}

abstract sig Pessoa {}
sig Professor extends Pessoa {}
sig Aluno extends Pessoa {}

abstract sig Atividade {}

sig Disciplina extends Atividade {
    professor: Professor,
    alunos: set Aluno,
}

sig AtividadeExtra extends Atividade {
    responsavel: Pessoa,
}

-- Predicado
pred mesmoDiaEHora[h1: Horario, h2: Horario]{
	(h1.dia = h2.dia and h1.hora = h2.hora) => h1 = h2
}

-- Predicado que verifica se o laboratório está disponível em determinado horário
pred laboratorioDisponivel(l: Lab, h: Horario) {
    no r: Reserva | r.horario = h and r.lab = l
}

-- Predicado que verifica se pessoa é professor
pred ehProfessor[p: Pessoa]{
	p in Professor
}

-- Predicado que verifica se atividade está na lista
pred atividadeNaFila(a: Atividade, h: Horario) {
    a in h.filaDeEspera
}

-- Fatos 

-- Fato que determina que cada horário seja único e não permitindo  que haja sobreposição de reservas no mesmo laboratório e no mesmo horário.
fact HorariosUnicos {
    all d:Dia | all h:Hora | d in Horario.dia and h in Horario.hora
    //no d:Dia | #{h:Horario | h.dia = d} < 4
    //no h:Hora | #{hor:Horario | hor.hora = h} < 5 

    all h1, h2: Horario | // Todos os horários são únicos
            mesmoDiaEHora[h1, h2]
    all r1, r2: Reserva | (r1.horario = r2.horario and r1.lab = r2.lab) => r1 = r2
}

-- Fato que determina restrições para as disciplinas
fact RestricoesDisciplinas {
    #Disciplina> 0
    all d:Disciplina | #d.alunos > 0
    all d:Disciplina | #d.professor = 1
    all d:Disciplina | 
            let rsd = {r:Reserva | r.atividade = d},
                    fsd = {h:Horario | d in h.filaDeEspera} | 
            (#rsd = 2 or #fsd = 2) and !(#rsd = 2 and #fsd = 2) and
            all r1, r2:rsd | 
                r1.horario.dia = r2.horario.dia => r1 = r2 and
            all f1, f2:fsd |
                f1.dia = f2.dia => f1 = f2
    
    no d:Disciplina | d in Horario.filaDeEspera and #{r:Reserva | r.atividade in Disciplina} < 40
}

-- Fato que determina restrições para as atividades extras e para fila de espera 

fact RestricoesFilaDeEspera {
    #AtividadeExtra > 0
    all a:AtividadeExtra | #{h:Horario | atividadeNaFila[a, h]} <= 1
    
    all r:Reserva | !(r.atividade in r.horario.filaDeEspera)
    no h:Horario | #h.filaDeEspera > 0 and #{r:Reserva | r.horario = h} < 2

    all a:Atividade | #{r:Reserva | r.atividade = a} > 0 or #{h:Horario | atividadeNaFila[a, h]} > 0
}

-- Fato que garante que o professor não possuirá duas disciplinas diferentes alocadas no mesmo horário 
fact RestricaoSoUmProfessorHorario{
	all p: Pessoa | all r1, r2: Reserva |
		ehProfessor[p] and r1.atividade in Disciplina and r2.atividade in Disciplina and
		r1.atividade.professor = p and r2.atividade.professor = p and
		r1 != r2 => r1.horario != r2.horario
}

-- Fato que garante que todas reservas de uma disciplinas serão feitas para um mesmo laboratório   
fact RestricoesReservasMesmoLaboratorio {
    all d: Disciplina | 
        let rsd = {r: Reserva | r.atividade = d} | 
        #rsd = 2 =>
            all r1, r2: rsd | r1.lab = r2.lab
}

-- Fato que garante que o professor não poderá alocar um horário para uma atividade extra quando já tiver sua disciplina reservada no mesmo horário 

fact RestricaoProfessorDisciplinaAtividadeExtra {
    all p: Pessoa |
        all r1: Reserva |
            ehProfessor[p] and r1.atividade in Disciplina and r1.atividade.professor = p =>
                no r2: Reserva |
                    r2.atividade in AtividadeExtra and 
                    r2.horario = r1.horario and 
                    r2.atividade.responsavel = p
}

-- Fato que garante que o número de horários deve ser igual ao de reservas 
fact RestricaoHorario {
	#Horario = #Reserva
}
-- Asserts

-- Teste para garantir que cada reserva deve ter um horário, um laboratório e uma atividade associada
assert TesteReservaCompleta {
    all r: Reserva | r.horario != none and r.lab != none and r.atividade != none
}
--check TesteReservaCompleta for 30

-- Teste para garantir que não há sobreposição de laboratórios
assert TesteReservasLabsDistintos {
    all r1, r2: Reserva |
        r1.lab = r2.lab and r1.horario = r2.horario => r1 = r2
}
--check TesteReservasLabsDistintos for 30

-- Teste para garantir que uma disciplina está alocada em apenas um laboratório
assert TesteMesmaDisciplinaMesmoLaboratorio {
    all d: Disciplina | 
        let reservas = {r: Reserva | r.atividade = d} |
        #reservas = 2 => 
            all r1, r2: reservas | r1.lab = r2.lab
}
--check TesteMesmaDisciplinaMesmoLaboratorio for 30

-- Teste para garantir que se há uma disciplina na lista de espera de um horário, não haverá uma atividade extra usando o laboratório no mesmo horário
assert TesteListaEsperaDisciplinaSemConflito {
    all h: Horario | 
        all d: Disciplina | 
            d in h.filaDeEspera => 
            no r: Reserva | r.horario = h and !(r.atividade in Disciplina)
}
--check TesteListaEsperaDisciplinaSemConflito for 30

-- Teste para garantir que um pedido da lista de espera para um dos LCCs pode ser contemplado em outro LCC se houver horário disponível.
assert TesteContemplacaoOutroLCC { 
    all h: Horario, l: Lab, a: Atividade | 
        a in h.filaDeEspera and 
        laboratorioDisponivel[l, h] => 
        some r2: Reserva | r2.horario = h and r2.lab != l and r2.atividade = a and 
        laboratorioDisponivel[r2.lab, h]
}
--check TesteContemplacaoOutroLCC for 30

-- Teste para garantir que se o professor fizer uma reserva, ele tem uma disciplina associada com dois horários semanais
assert TesteProfAssocDisciplinaComDoisHorarios {
    all p: Professor |
        some r: Reserva | r.atividade.professor = p =>
            let d = r.atividade |
            #({r: Reserva | r.atividade = d}) = 2
}
--check TesteProfAssocDisciplinaComDoisHorarios for 30

-- Teste para garantir que as reservas só podem ser feitas com duração de duas horas por dia
assert TesteReservasDuasHoras {
    all r: Reserva |
        one r.horario // Garante que a reserva tem exatamente um horário (ou seja, duas horas)
}
--check TesteReservasDuasHoras for 30

-- Teste para garantir que há uma lista de espera por horário e por laboratório
assert TesteListaDeEsperaPorHorarioEPorLab {
    all h: Horario | all l: Lab |
        some h.filaDeEspera =>
            some r: Reserva | r.horario = h and r.lab = l
}
--check TesteListaDeEsperaPorHorarioEPorLab for 30

-- Teste para garantir que uma disciplina não estará simultaneamente reservada e na lista de espera.
assert TesteNumReservasDisciplinas {
    all d: Disciplina |
        let reservaD = {r: Reserva | r.atividade = d},
            filaD = {h: Horario | d in h.filaDeEspera} |
        (#reservaD = 2 and #filaD = 0) or (#reservaD = 0 and #filaD = 2)
}
-- check TesteNumReservasDisciplinas for 30

-- Teste para garantir que cada professor não poderá reservar o mesmo horário mais de uma vez
assert TesteUmaReservaProfessorPorHorario {
    all p: Professor | 
        all r1, r2: Reserva | 
        r1.atividade in Disciplina and r2.atividade in Disciplina and
        r1.atividade.professor = p and r2.atividade.professor = p and
        r1 != r2 => r1.horario != r2.horario
}
-- check TesteUmaReservaProfessorPorHorario for 30

-- Teste para garantir que uma atividade que já está reservada não poderá estar na fila de espera
assert TesteAtivReservadaListaEspera {
    all r: Reserva | !(r.atividade in r.horario.filaDeEspera)
}

-- check TesteAtivReservadaListaEspera for 30

-- Teste para garantir que um professor não pode alocar um lab para uma atividade extra se já estiver alocado uma disciplina no mesmo horário
assert TesteProfessorDisciplinaAtividadeExtra {
    all p: Professor |
        all r1: Reserva | 
            r1.atividade in Disciplina and r1.atividade.professor = p =>
                no r2: Reserva |
                    r2.atividade in AtividadeExtra and r2.horario = r1.horario and r2.atividade.responsavel = p
}

--check TesteProfessorDisciplinaAtividadeExtra for 30

-- Teste para garantir que o professor não tenha duas disciplinas com horários sobrepostos
assert TesteProfcom2DiscSobrepostas { 
all p: Professor | no r1, r2: Reserva | r1.atividade.professor = p and r2.atividade.professor = p and r1.atividade != r2.atividade and r1.horario = r2.horario
 } 
-- check TesteProfcom2DiscSobrepostas for 30 

-- Teste para garantir que os horários são únicos para cada reserva de laboratório
assert TesteHorariosUnicos { 
all r1, r2: Reserva | !(r1 != r2 and r1.horario = r2.horario and r1.lab = r2.lab) 
}
 -- check TesteHorariosUnicos for 30 

-- Teste para garantir que é professor 
assert TesteEhProfessor { 
all p: Pessoa | ehProfessor[p] => p in Professor
 } 
-- check TesteEhProfessor for 30 

-- Teste para garantir que todas as disciplinas tenham  pelo menos um aluno associado a elas
assert TesteDisciplinaComAlunos { 
no d: Disciplina | #d.alunos = 0 
}
 -- check TesteDisciplinaComAlunos for 30 

-- Teste para garantir que cada disciplina tenha exatamente um professor 
assert TesteUmProfessorPorDisciplina {
 no d: Disciplina | #d.professor != 1 
} 
 -- check TesteUmProfessorPorDisciplina for 30

-- Teste para garantir que uma atividade não ocupa mais que uma vaga na fila de espera.
assert TesteNumFilaAtv {
    all a: AtividadeExtra |
        let filaD = {h: Horario | a in h.filaDeEspera} |
        !(#filaD > 1)
}

 -- check TesteNumFilaAtv for 30
run {} for 30
