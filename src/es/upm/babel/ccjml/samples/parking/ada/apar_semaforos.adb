--  apar_semaforos.adb --  Control de aparcamiento con semáforos
--
--  Author : Manuel Carro


with Semaphores;
use Semaphores;

with Conc_IO;
use Conc_IO;

with Ada.Numerics.Float_Random;
use Ada.Numerics.Float_Random;


--  Este programa es ligeramente diferente del explicado en clase : en
--  lugar de tener una barrera de entrada y de salida a la que llegan
--  los coches, son estos los que deciden cuando pueden entrar o no al
--  aparcamiento.  No implementa, por tanto, los procesos que
--  controlan las barreras de entrada y salida, sino que son los
--  coches los que llaman directamente al recurso compartido.



procedure Apar_Semaforos is

   --  Número de coches y cuanto tardan en comprar y en dar vueltas
   NCoches : constant Natural := 18;
   Tiempo_Fuera : constant Float := 0.1;
   Tiempo_Dentro : constant Float := 0.1;

   --  Control de entrada y salida
   Vacio : Bin_Semaphore;

   task type Tipo_Coche;
   task body Tipo_Coche is
      G : Generator;
   begin
      loop
         --  Dando vueltas
         delay Duration (Random (G) * Tiempo_Fuera);
         --  Intentando entrar
         Put_Line ("Coche quiere entrar");
         Wait (Vacio);
         Put_Line ("Coche entró");
         --  Comprando
         delay Duration (Random (G) * Tiempo_Dentro);
         --  Saliendo
         Signal (Vacio);
         Put_Line ("Coche salió");
      end loop;
   end Tipo_Coche;


   Coches : array (1 .. NCoches) of Tipo_Coche;

begin
   null;
end Apar_Semaforos;
