--  lecsescs_msg.adb --  lectores escritores con vivacidad y con Rendez-Vous
--
--  Author : MCL

--  with Ada.Text_IO;
--  use Ada.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Lectores_Escritores_RV is

   --  Cada lector y escritor usa este tiempo como base para determinar
   --  lo que dura una lectura y una escriture, pero cada proceso
   --  tiene una duración real distinta calculada teniendo en cuenta si
   --  identificador.
   Tiempo_Lectura : constant Duration := 0.7;
   Tiempo_Escritura : constant Duration := 1.0;

   --  Cuantos lectores y escritores hay.
   Num_Procs_Lectores : constant Positive := 1;
   Num_Procs_Escritores : constant Positive := 3;

   subtype Tipo_Ident_Lector is Positive range  1 .. Num_Procs_Lectores;
   subtype Tipo_Ident_Escritor is Positive range  1 .. Num_Procs_Escritores;


   --  Código del gestor de lectores y escritores.  El objeto (monitor)
   --  activo aguarda peticiones y las atiende cuando pueden ser
   --  satisfechas.

   task type Gestor_LE is
      entry Comenzar_Lectura;
      entry Comenzar_Escritura;
      entry Terminar_Lectura;
      entry Terminar_Escritura;
   end Gestor_LE;

   --  El estado es el mismo que para la implementación de objetos
   --  protegidos.
   task body Gestor_LE is
      Num_Lectores : Natural := 0;
      Escribiendo : Boolean := False;
      Turnolector : Boolean := False;
   begin
      loop
         select
            when not Escribiendo and
              (Comenzar_Escritura'Count = 0 or Turnolector) =>
               accept Comenzar_Lectura do
                  Num_Lectores := Num_Lectores + 1;
               end Comenzar_Lectura;
         or
            when Num_Lectores = 0 and
              not Escribiendo and
              (Comenzar_Lectura'Count = 0 or not Turnolector) =>
               accept Comenzar_Escritura do
                  Escribiendo := True;
               end Comenzar_Escritura;
         or
            when True =>
               accept Terminar_Lectura do
                  Num_Lectores := Num_Lectores - 1;
                  Turnolector := False;
               end Terminar_Lectura;
         or
            when True =>
               accept Terminar_Escritura do
                  Escribiendo := False;
                  Turnolector := True;
               end Terminar_Escritura;
         end select;
      end loop;
   end Gestor_LE;


   Gestor : Gestor_LE;

   --  Código de las tareas.  Para este caso es idéntico al de objetos
   --  protegidos.

   task type Lector (Ident : Tipo_Ident_Lector := 1);
   task body Lector is
   begin
      loop
         Put_Line ("Lector "&Tipo_Ident_Lector'Image (Ident)&" quiere leer");
         Gestor.Comenzar_Lectura;
         Put_Line ("Lector "&Tipo_Ident_Lector'Image (Ident)& " lee");
         delay Tiempo_Lectura * Duration (Ident);
         Gestor.Terminar_Lectura;
         Put_Line ("Lector "&Tipo_Ident_Lector'Image (Ident)& " termina");
      end loop;
   end Lector;


   task type Escritor (Ident : Tipo_Ident_Escritor := 1);
   task body Escritor is
   begin
      loop
         Put_Line ("Escritor " &
                   Tipo_Ident_Escritor'Image (Ident) &
                   " quiere escribir");
         Gestor.Comenzar_Escritura;
         Put_Line ("Escritor " &
                   Tipo_Ident_Escritor'Image (Ident) &
                   " escribe");
         delay Tiempo_Escritura * Duration (Ident);
         Gestor.Terminar_Escritura;
         Put_Line ("Escritor " &
                   Tipo_Ident_Escritor'Image (Ident) &
                   " termina");
      end loop;
   end Escritor;

   type Escritor_P is access Escritor;
   type Lector_P is access Lector;

   Lectores : array (Tipo_Ident_Lector) of Lector_P;
   Escritores : array (Tipo_Ident_Escritor) of Escritor_P;

begin
   for I in Tipo_Ident_Lector loop
      Lectores (I) := new Lector (I);
   end loop;

   for I in Tipo_Ident_Escritor loop
      Escritores (I) := new Escritor (I);
   end loop;
end Lectores_Escritores_RV;
