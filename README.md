# Logica
## Projeto feito com a linguagem Alloy para a disciplina de Lógica



Submeta uma especificação em Alloy com o seguinte sistema:
A UFCG vai implantar um sistema de reserva dos laboratórios LCC1 e LCC2 semanalmente.
As reservas só podem ser feitas com duração de duas horas por dia. O quatro horários possíveis:
8h-10h, 10h-12h, 14h-16h,16h-18h (nos 5 dias úteis da semana).
Se o professor reservar, é que tem uma disciplina associada, com dois horários semanais.
Existe uma lista de espera por horário e por sala. Em nenhum momento a lista de espera tem um horário de disciplina enquanto outro horário sem disciplina está usando a sala. Um pedido da lista de espera para um dos LCCs pode ser contemplado em outro LCC se houver horário disponível.

Instruções adicionais
Apenas um integrante do grupo (de até 6 integrantes) envia o resultado do exercício. A resposta ao exercício deve incluir o nome completo de todos, e o anexo deve conter o arquivo alloy.

Vamos cobrar clareza, legibilidade e comentários explicativos na correção.
É obrigatório o uso de asserts para verificação de propriedades acerca da especificação.
Texto de resposta
conjunto: LCC1 e LCC2
horarios: 8-10; 10-12; 14-16; 16-18
