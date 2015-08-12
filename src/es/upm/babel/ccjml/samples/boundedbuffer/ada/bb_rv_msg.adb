--  buffer_msg.adb -- productor / servidor / consumidor con mensajes y
--  canales explícitos
--
--  Author : MCL


--  El buffer de entrada / salida es un paquete separado, para poder
--  utilizarlo en varios sitios.
with Buffers;

--  El canal es un recurso separado, que empleamos para comunicar
--  tareas explícitamente.
with Channels;

with Ada.Text_IO;
use Ada.Text_IO;

--  with Conc_IO;
--  use Conc_IO;

procedure Bb_Rv_Msg is

   --  Tamaño del buffer
   Tam_Buffer : constant Positive := 10;

   --  Creamos el buffer en sí.  También podríamos, perfectamente,
   --  hacer una definición local de un buffer, incluso dentro de la
   --  tarea servidora.
   package Buffer_Int is
      new Buffers (Integer);
   use Buffer_Int;

   --  Número de productores y consumidores
   NCons : constant Positive := 6;
   NProd : constant Positive := 3;

   --  Un canal para transmitirnos enteros
   package Channel_Int is
      new Channels (Integer);
   use Channel_Int;

   --  Definición del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Item : in Integer);
      entry Tomar (Chan : in out Channel);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is
       Buf : Buffer (Tam_Buffer);
      Item : Integer;
      Pending_Channel : Channel;
   begin
      Crear_Vacio (Buf);
      loop
         --  Bucle  infinito  esperando   por  una  petición,  que  es
         --  admitida accediendo al buffer externo.  Ahora las entries
         --  no  tienen  condicion de  bloqueo,  sino  que se  guarda,
         --  internamente, la  peticion.  El servidor  provee un canal
         --  de comunicación  sobre el que esperar y  recibir el dato.
         --  Como aproximacion,  realizamos una atención  por orden de
         --  llegada  (similar a  la  atención uno  a  uno en  objetos
         --  protegidos).
         select
            when N_Huecos (Buf) > 0 =>
               accept Poner (Item : in Integer) do
                  Insertar (Buf, Item);
               end Poner;
         or
            when N_Datos (Buf) > 0 =>
               accept Tomar (Chan : in out Channel) do
                  Pending_Channel := Chan;
                  Primero (Buf, Item);
                  Borrar (Buf);
               end Tomar;
               Send (Pending_Channel, Item);
         end select;
      end loop;
   end BufServer;

   --  Variable que representa la tarea servidora
   TheBufServer : BufServer;

   --  Definición de los productores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Productor;
   task body Productor is
      Dato : Natural := 0;
   begin
      loop
         TheBufServer.Poner (Dato);
         Put_Line ("Productor envió " & Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
      end loop;
   end Productor;


   --  Definición de los consumidores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Consumidor;
   task body Consumidor is
      Dato : Natural;
      My_Channel : Channel;
   begin
      Create (My_Channel);
      loop
         TheBufServer.Tomar (My_Channel); --  Pedimos que nos manden el
                                          --  dato, y decimos por qué
                                          --  canal lo vamos a esperar
         Receive (My_Channel, Dato);
         Put_Line ("Consumidor obtuvo " & Integer'Image (Dato));
         delay 0.5;
      end loop;
   end Consumidor;


   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheConsumers : array (1 .. NCons) of Consumidor;

begin --  Principal
   null;
end Bb_Rv_Msg;
