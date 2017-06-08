--  Solución sin vivacidad para el problema de los lectores/escritores
--  Adapación a Ada 95 : Jaime Ramírez.

--  En esta solución se puede observar muy bien la inanición de las tareas
--  escritoras

--  with Ada.Text_IO;
--  use Ada.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Lectores_Escritores_Seg is

   Pausa : constant Duration := 5.0;

   Num_Lectores : constant Positive := 3;
   Numescritores : constant Positive := 3;

   subtype Tipo_Identidad_Lector is Positive range  1 .. Num_Lectores;
   subtype Tipo_Identidad_Escritor is Positive range  1 .. Numescritores;


   --  Código del gestor

   protected type Tipo_Gestor is
      entry Comenzar_Lectura;
      entry Comenzar_Escritura;
      entry Terminar_Lectura;
      entry Terminar_Escritura;
   private
      Num_Lectores : Natural := 0;
      Escribiendo : Boolean := False;
   end Tipo_Gestor;


   protected body Tipo_Gestor is

      entry Comenzar_Lectura when
        not Escribiendo is
      begin
         Num_Lectores := Num_Lectores + 1;
      end Comenzar_Lectura;

      entry Comenzar_Escritura when
        Num_Lectores = 0 and not Escribiendo is
      begin
         Escribiendo := True;
      end Comenzar_Escritura;

      entry Terminar_Lectura when True is
      begin
         Num_Lectores := Num_Lectores - 1;
      end Terminar_Lectura;

      entry Terminar_Escritura when True is
      begin
         Escribiendo := False;
      end Terminar_Escritura;
   end Tipo_Gestor;


   Gestor : Tipo_Gestor;

   --  Código de las tareas

   task type Lector (Ident : Tipo_Identidad_Lector := 1);
   task body Lector is
   begin
      loop
         Put_Line ("Lector "&Tipo_Identidad_Lector'Image (Ident)&
                   " quiere leer");

         Gestor.Comenzar_Lectura;

         Put_Line ("Lector "&Tipo_Identidad_Lector'Image (Ident)&
                   " lee");
         delay Pausa;

         Gestor.Terminar_Lectura;

         Put_Line ("Lector "&Tipo_Identidad_Lector'Image (Ident)&
                   " termina de leer");
      end loop;
   end Lector;


   task type Escritor (Ident : Tipo_Identidad_Escritor := 1);
   task body Escritor is
   begin
      loop
         Put_Line ("Escritor "&Tipo_Identidad_Escritor'Image (Ident)&
                   " quiere escribir");

         Gestor.Comenzar_Escritura;

         Put_Line ("Escritor "&Tipo_Identidad_Escritor'Image (Ident)&
                   " escribe");
         delay Pausa;

         Gestor.Terminar_Escritura;

         Put_Line ("Escritor "&Tipo_Identidad_Escritor'Image (Ident)&
                   " termina de escribir");

      end loop;
   end Escritor;

   --  Lectores : array (Tipo_Identidad_Lector) of Lector;
   --  Escritores : array (Tipo_Identidad_Escritor) of Escritor;

   Lector1 : Lector (1);
   Lector2 : Lector (2);
   Lector3 : Lector (3);

   Escritor1 : Escritor (1);
   Escritor2 : Escritor (2);
   Escritor3 : Escritor (3);

begin
   null;
end Lectores_Escritores_Seg;

