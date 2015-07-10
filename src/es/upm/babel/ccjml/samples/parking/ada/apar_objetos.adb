--  apar_objetos.adb --  Control de aparcamiento con objetos protegidos
--
--  Author : Manuel Carro

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


procedure Apar_Objetos is

   --  Número de coches y cuanto tardan en comprar y en dar vueltas
   NCoches : constant Natural := 15;
   Tiempo_Fuera : constant Float := 2.0;
   Tiempo_Dentro : constant Float := 4.0;

   --  Máximo de coches en el aparcamiento
   --  Tam_Aparc : constant Natural := NCoches / 3;
   Tam_Aparc : constant Natural := 1;

   --  Este recurso compartido representa el aparcamiento; su estado es el
   --  número de sitios vacios en él.
   protected type Tipo_Aparcamiento is
      --  La entrada en un coche se puede hacer cuando hay sitios libre
      entry Entrar;
      --  La salida de un coche se puede realizar en cualquier momento
      entry Salir;
   private
      --  Lo único que necesitamos guardar es cuantos sitios libres
      --  tenemos  el sistema de guardas de Ada se encarga del resto.
      Sitios_Vacios : Integer := Tam_Aparc;
   end Tipo_Aparcamiento;

   --  Implementación del tipo protegido
   protected body Tipo_Aparcamiento is
      entry Entrar
      when Sitios_Vacios > 0 is
      begin
         Sitios_Vacios := Sitios_Vacios - 1;
         if Sitios_Vacios < 0 then
            Put_Line ("Han entrado demasiado coches!!!!");
         end if;
      end Entrar;

      entry Salir when True is
      begin
         Sitios_Vacios := Sitios_Vacios + 1;
      end Salir;
   end Tipo_Aparcamiento;

   Aparcamiento : Tipo_Aparcamiento;

   task type Tipo_Coche;
   task body Tipo_Coche is
      G : Generator;
   begin
      loop
         --  Dando vueltas
         delay Duration (Random (G) * Tiempo_Fuera);
         --  Intentando entrar
         Put_Line ("Coche quiere entrar");
         Aparcamiento.Entrar;
         Put_Line ("Coche entró");
         --  Comprando
         delay Duration (Random (G) * Tiempo_Dentro);
         --  Saliendo
         Put_Line ("Coche va a salir");
         Aparcamiento.Salir;
         Put_Line ("Coche salió");
      end loop;
   end Tipo_Coche;


   Coches : array (1 .. NCoches) of Tipo_Coche;

begin
   null;
end Apar_Objetos;
