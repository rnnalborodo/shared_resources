--  buffer_msg_dbloq.adb : buffer acotado con bloqueo en dos fases
--  (atención uno a uno en orden de llegada) para simplificar el
--  almacenamiento de las llamadas pendientes.
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

procedure Bb_Msg_Dbloq is

   --  Tamaño del buffer
   Tam_Buffer : constant Positive := 10;

   --  Creamos el buffer en sí.  También podríamos, perfectamente,
   --  hacer una definición local de un buffer, incluso dentro de la
   --  tarea servidora.
   package Buffer_Int is
      new Buffers (Integer);
   use Buffer_Int;


   --  Número de productores y consumidores
   NCons : constant Positive := 8;
   NProd : constant Positive := 3;

   --  Un canal para transmitirnos enteros
   package Channel_Int is
      new Channels (Integer);
   use Channel_Int;

   --  Definición del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Chan : in out Channel);
      entry Tomar (Chan : in out Channel);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is
      Buf : Buffer (Tam_Buffer);
      Item : Integer;
      Delayed_Get_Chan,
      Delayed_Put_Chan : Channel;
      Delayed_Get : Boolean := False;
      Delayed_Put : Boolean := False;
      Local_Channel : Channel;
   begin
      Crear_Vacio (Buf);
      loop
         --  Bucle  infinito  esperando   por  una  petición,  que  es
         --  admitida accediendo al buffer externo.  Ahora las entries
         --  no  tienen  condicion de  bloqueo,  sino  que se  guarda,
         --  internamente, la  peticion.  El servidor  provee un canal
         --  de comunicación  sobre el que esperar y  recibir el dato.
         --  Sólo  guardamos una  petición  cada vez,  y no  aceptamos
         --  nuevas peticiones hasta haber satisfecho la pendiente.
         select
            when not Delayed_Put =>
               accept Poner (Chan : in out Channel) do
                  Local_Channel := Chan;
               end Poner;
               if N_Huecos (Buf) = 0 then
                  Delayed_Put := True;
                  Delayed_Put_Chan := Local_Channel;
               else
                  Receive (Local_Channel, Item);
                  Insertar (Buf, Item);
                  if Delayed_Get then
                     Primero (Buf, Item);
                     Borrar (Buf);
                     Send (Delayed_Get_Chan, Item);
                     Delayed_Get := False;
                  end if;
               end if;
         or
            when not Delayed_Get =>
               accept Tomar (Chan : in out Channel) do
                  Local_Channel := Chan;
               end Tomar;
               if N_Datos (Buf) = 0 then
                  Delayed_Get := True;
                  Delayed_Get_Chan := Local_Channel;
               else
                  Primero (Buf, Item);
                  Borrar (Buf);
                  Send (Local_Channel, Item);
                  if Delayed_Put then
                     Receive (Delayed_Put_Chan, Item);
                     Insertar (Buf, Item);
                     Delayed_Put := False;
                  end if;
               end if;
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
      My_Channel : Channel;
   begin
      Create (My_Channel);
      loop
         TheBufServer.Poner (My_Channel);
         Send (My_Channel, Dato);
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
         delay 0.1;
      end loop;
   end Consumidor;


   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheConsumers : array (1 .. NCons) of Consumidor;

begin --  Principal
   null;
end Bb_Msg_Dbloq;
