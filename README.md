<h1 align="center">
    <img title="a title" alt="Alt text" src="https://iconape.com/wp-content/files/vm/195950/png/ufcg_universidade_federal_de_campina_grande-logo.png" height=150 >
  <p> Lógica Para Computação - Prof. Tiago Massoni </p>
</h1>

# Mini-projeto usando Alloy - ReservaLCC

## Integrantes: 

- [Caio Cesar Vieira Cavalcanti](https://github.com/Caio-Cesar-Vieira-Cavalcanti)
- [João Lucas Gomes Brandão](https://github.com/Joaogomesbrandao)
- [João Pedro Azevedo do Nascimento](https://github.com/jpedro8azevedo)
- [Valdemar Victor Leite Carvalho](https://github.com/valdemarvictorleitecarvalho)
- [Vinícius de Oliveira Porto](https://github.com/viniciusdeoliveiraporto)
- [Walber Wesley Félix de Araújo Filho](https://github.com/walber-araujo)

## Especificação:

A UFCG vai implantar um sistema de reserva dos laboratórios LCC1 e LCC2 semanalmente.


As reservas só podem ser feitas com duração de duas horas por dia. O quatro horários possíveis:

8h-10h, 10h-12h, 14h-16h,16h-18h (nos 5 dias úteis da semana).
Se o professor reservar, é que tem uma disciplina associada, com dois horários semanais.

Existe uma lista de espera por horário e por sala. Em nenhum momento a lista de espera tem um horário de disciplina enquanto outro horário sem disciplina está usando a sala. Um pedido da lista de espera para um dos LCCs pode ser contemplado em outro LCC se houver horário disponível.

> É obrigatório o uso de asserts para verificação de propriedades acerca da especificação.
