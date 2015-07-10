--  apar_incontrolado.adb --  Control de aparcamiento con variables compartidas
--
--  Author : Manuel Carro

with Ada.Text_IO;
use  Ada.Text_IO;

--  with Conc_Io;
--  use Conc_Io;

with Ada.Numerics.Float_Random;
use Ada.Numerics.Float_Random;


--  Este programa es ligeramente diferente del explicado en clase: en
--  lugar de tener una barrera de entrada y de salida a la que llegan
--  los coches, son estos los que deciden cuando pueden entrar o no al
--  aparcamiento.  No implementa, por tanto, los procesos que
--  controlan las barreras de entrada y salida, sino que son los
--  coches los que llaman directamente al recurso compartido.


procedure Apar_Incontrolado is

   --  Número de coches y cuánto tardan en comprar y en dar vueltas
   NCoches : constant Natural := 18;
   Tiempo_Fuera : constant Float := 0.01;
   Tiempo_Dentro : constant Float := 0.01;

   --  Máximo de coches en el aparcamiento
   Tam_Aparc : constant Natural := 4;

   --  Control de entrada y salida
   Coches_Dentro : Natural := 0;

   task type Tipo_Coche (C : Natural);
   task body Tipo_Coche is
      G : Generator;
      Espacio : Boolean;
   begin
      loop
         --  Dando vueltas
         delay Duration (Random (G) * Tiempo_Fuera);
         --  Llegamos a barrera, intentamos entrar
         Put_Line ("Coche" & Natural'Image (C) & " quiere entrar");
         Espacio := False;
         while not Espacio loop
            if Coches_Dentro < Tam_Aparc then
               Espacio := True;
               Coches_Dentro := Coches_Dentro + 1;
            end if;
         end loop;
         Put_Line ("Coche" & Natural'Image (C) & " entró");
         --  Comprobamos si se ha excedido el tamaño del aparcamiento
         if Coches_Dentro > Tam_Aparc then
            Put_Line ("====== Demasiados coches en el aparcamiento ======");
         end if;
         delay Duration (Random (G) * Tiempo_Dentro);
         --  Comprobamos de nuevo .. .
         if Coches_Dentro > Tam_Aparc then
            Put_Line ("====== Demasiados coches en el aparcamiento ======");
         end if;
         --  Saliendo : decrementamos número de coches en el aparcamiento
         Coches_Dentro := Coches_Dentro - 1;
         Put_Line ("Coche" & Natural'Image (C) & " salió");
      end loop;
   end Tipo_Coche;

   type Tipo_Coche_P is access Tipo_Coche;

   Coches : array (1 .. NCoches) of Tipo_Coche_P;

begin
   for I in 1 .. NCoches loop
      Coches (I) := new Tipo_Coche (I);
   end loop;
   loop
      Put_Line ("*** Coches en aparcamiento : " &
                Natural'Image (Coches_Dentro));
      delay 0.1;
   end loop;
end Apar_Incontrolado;
