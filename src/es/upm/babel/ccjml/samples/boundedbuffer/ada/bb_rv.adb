--  buffer_rv.adb --  productor / servidor / consumidor con Rendez-Vous
--
--  Author : MCL


with Buffers;

--  with ADA.Text_IO;
--  use ADA.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Bb_RV is

   --  Tama�o del buffer
   Tam_Buffer : constant Positive := 10;

   --  Creamos el buffer en s�.  Tambi�n podr�amos, perfectamente,
   --  hacer una definici�n local de un buffer, incluso dentro de la
   --  tarea servidora.
   package Buffer_Int is
      new Buffers (Integer);
   use Buffer_Int;

   --  N�mero de productores y consumidores
   NCons : constant Positive := 6;
   NProd : constant Positive := 3;


   --  Definici�n del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Item : in Integer);
      entry Tomar (Item : out Integer);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is
      --  El buffer se crea inicialmente vac�o (porque lo asegura el
      --  paquete correspondiente; de no ser as� habr�a que hacerlo
      --  vac�o expl�citamente)
      Buf : Buffer (Tam_Buffer);
   begin
      Crear_Vacio (Buf);
      loop
         --  Bucle  infinito  esperando   por  una  petici�n,  que  es
         --  admitida accediendo al  buffer externo.  Cada entry tiene
         --  una condici�n  que se refiere al estado  de las variables
         --  locales de la tarea.
         select
            when N_Huecos (Buf) > 0 =>
               accept Poner (Item : in Integer) do
                  Insertar (Buf, Item);
               end Poner;
         or
            when N_Datos (Buf) > 0 =>
               accept Tomar (Item : out Integer) do
                  Primero (Buf, Item);
                  Borrar (Buf);
               end Tomar;
         end select;
      end loop;
   end BufServer;

   --  Variable que representa la tarea servidora
   TheBufServer : BufServer;

   --  Definici�n de los productores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Productor;
   task body Productor is
      Dato : Natural := 0;
   begin
      loop
         TheBufServer.Poner (Dato);
         Put_Line ("Productor envi� " &
                   Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
      end loop;
   end Productor;

   --  Definici�n de los consumidores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Consumidor;
   task body Consumidor is
      Dato : Natural;
   begin
      loop
         TheBufServer.Tomar (Dato); --  pedimos que nos manden el dato
         Put_Line ("Consumidor obtuvo " &
                   Integer'Image (Dato));
         delay 0.5;
      end loop;
   end Consumidor;

   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheConsumers : array (1 .. NCons) of Consumidor;

begin --  Principal
   null;
end Bb_RV;
