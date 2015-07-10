--  apar_objetos.adb -- Control de aparcamiento con Rendez-Vous.
--  Atenci�n al modo en que se realizan las acciones sobre el estado
--  en el interior de la tarea.
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
procedure Apar_RV is

   --  N�mero de coches y cuanto tardan en comprar y en dar vueltas
   NCoches : constant Natural := 15;
   Tiempo_Fuera : constant Float := 2.0;
   Tiempo_Dentro : constant Float := 4.0;

   --  M�ximo de coches en el aparcamiento : menos que los que hay en
   --  nuestro peque�o mundo.
   Tam_Aparc : constant Natural := NCoches / 3;

   --  Este recurso compartido representa el aparcamiento; su estado es el
   --  n�mero de sitios vacios en �l.
   task type Tipo_Aparcamiento is
      --  La entrada en un coche se puede hacer cuando hay sitios libres
      entry Entrar;
      --  La salida de un coche se puede realizar en cualquier momento
      entry Salir;
   end Tipo_Aparcamiento;



   --  Implementaci�n del tipo protegido.  Como no hay paso de
   --  argumentos en ning�n sentido, se pueden dejar las acciones que
   --  cambian el estado del recurso *fuera* de los do/end de los
   --  accept.  No hay problema de concurrencia en ese cambio, pues es
   --  una �nica tarea la que recorre el bucle.  Tampoco hay problema
   --  de observaci�n de ese cambio en un momento inadecuado desde el
   --  exterior, porque la �nica interacci�n con el estado es a trav�s
   --  de los accept : se estar� preparado para aceptar una nueva
   --  llamada cuando ya haya acabado el cambio de las variables
   --  locales.
   task body Tipo_Aparcamiento is
      Sitios_Vacios : Natural := Tam_Aparc;
   begin
      loop
         select
            when Sitios_Vacios > 0 =>
               accept Entrar do
                  null;
               end Entrar;
               Sitios_Vacios := Sitios_Vacios - 1;
         or
            when True =>
               accept Salir do
                  null;
               end Salir;
               Sitios_Vacios := Sitios_Vacios + 1;
         end select;
      end loop;
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
         Put_Line ("Coche entr�");
         --  Comprando
         delay Duration (Random (G) * Tiempo_Dentro);
         --  Saliendo
         Aparcamiento.Salir;
         Put_Line ("Coche sali�");
      end loop;
   end Tipo_Coche;


   Coches : array (1 .. NCoches) of Tipo_Coche;

begin
   null;
end Apar_RV;
