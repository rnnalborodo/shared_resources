--  Solución con vivacidad para el problema de los lectores/escritores


--  with Ada.Text_IO;
--  use Ada.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Lectores_Escritores_Op is


   Num_Procs_Lectores : constant Positive := 6;
   Num_Procs_Escritores : constant Positive := 6;

   subtype Tipo_Identidad_Lector is
     Positive range  1 .. Num_Procs_Lectores;
   subtype Tipo_Identidad_Escritor is
     Positive range  1 .. Num_Procs_Escritores;


   --  Código del gestor

   protected type Tipo_Gestor is
      entry Comenzar_Lectura;
      entry Comenzar_Escritura;
      procedure Terminar_Lectura;
      procedure Terminar_Escritura;
   private
      Num_Lectores : Natural := 0;
      Escribiendo : Boolean := False;
      Turnolector : Boolean := False;
   end Tipo_Gestor;


   protected body Tipo_Gestor is

      entry Comenzar_Lectura when
        not Escribiendo and
        (Comenzar_Escritura'Count = 0 or Turnolector) is
      begin
         Num_Lectores := Num_Lectores + 1;
      end Comenzar_Lectura;

      entry Comenzar_Escritura when
        Num_Lectores = 0 and not Escribiendo and
        (Comenzar_Lectura'Count = 0 or not Turnolector) is
      begin
         Escribiendo := True;
      end Comenzar_Escritura;

      procedure Terminar_Lectura is
      begin
         Num_Lectores := Num_Lectores - 1;
         Turnolector := False;
      end Terminar_Lectura;

      procedure Terminar_Escritura is
      begin
         Escribiendo := False;
         Turnolector := True;
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
         delay 5.0;

         Gestor.Terminar_Lectura;

         Put_Line ("Lector "&Tipo_Identidad_Lector'Image (Ident)&
                   " termina");
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
         delay 5.0;

         Gestor.Terminar_Escritura;

         Put_Line ("Escritor "&Tipo_Identidad_Escritor'Image (Ident)&
                   " termina");

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
end Lectores_Escritores_Op;
