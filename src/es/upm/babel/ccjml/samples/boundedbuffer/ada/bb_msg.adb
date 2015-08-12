--  buffer_msg.adb: productor / servidor / consumidor con mensajes y
--  canales explícitos


--  Author : MCL


with Ada.Exceptions;
use Ada.Exceptions;

--  El buffer de entrada / salida es un paquete separado, para poder
--  utilizarlo en varios sitios.
with Buffers;

--  El canal es un recurso separado, que empleamos para comunicar
--  tareas explícitamente.
with Channels;

--  Colas para almancenar las peticiones almacenadas
with Colas;

--  with ADA.Text_IO;
--  use ADA.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Bb_Msg is

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

   --  Cola de peticiones pendientes, cada una representada por su
   --  canal.  En este caso no necesitamos almacenar más datos
   --  asociados a cada llamada.
   package Colas_Chan_Int is
      new Colas (Channel);
   use Colas_Chan_Int;

   --  Definición del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Chan : in out Channel);
      entry Tomar (Chan : in out Channel);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is
      --  El buffer se crea inicialmente vacío (porque lo asegura el
      --  paquete correspondiente; de no ser así habría que hacerlo
      --  vacío explícitamente)
      Buf : Buffer (Tam_Buffer);
      Item : Integer;
      Cola_Poner_Pendiente : Cola;
      Cola_Tomar_Pendiente : Cola;
      Rec_Chan, Send_Chan : Channel;
      Name_Error : exception;
   begin
      Crear_Vacio (Buf);
      loop
         --  Bucle  infinito  esperando   por  una  petición,  que  es
         --  admitida accediendo al buffer externo.  Ahora las entries
         --  no  tienen  condicion de  bloqueo,  sino  que se  guarda,
         --  internamente, la  peticion.  El servidor  provee un canal
         --  de comunicación  sobre el que esperar y  recibir el dato.
         --  En esta  version guardamos  todas las peticiones  que nos
         --  van  llegando y las  satisfacemos hasta  el nivel  que se
         --  pueda.  Este problema no exige este nivel de afinamiento,
         --  pero sirve para ilustrar cómo se puede tratar un caso más
         --  complejo.
         select
            when True =>
               accept Poner (Chan : in out Channel) do
                  --  Almacenar peticion como pendiente
                  Insertar (Cola_Poner_Pendiente, Chan);
               end Poner;
         or
            when True =>
               accept Tomar (Chan : in out Channel) do
                  --  Almacenar peticion como pendiente
                  Insertar (Cola_Tomar_Pendiente, Chan);
               end Tomar;
         end select;
         --  Tratar las peticiones pendientes.  ¿Puede separarse en dos
         --  bucles, uno tras cada accept?
         while
           (not Es_Vacia (Cola_Tomar_Pendiente)
            and N_Datos (Buf) > 0) or
           (not Es_Vacia (Cola_Poner_Pendiente)
            and N_Huecos (Buf) > 0) loop

            if (not Es_Vacia (Cola_Tomar_Pendiente)
                and N_Datos (Buf) > 0) then --  Aceptamos un tomar
               Primero (Cola_Tomar_Pendiente, Send_Chan);
               Borrar (Cola_Tomar_Pendiente);
               Primero (Buf, Item);
               Borrar (Buf);
               Send (Send_Chan, Item);
            end if;

            if (not Es_Vacia (Cola_Poner_Pendiente)
                and N_Huecos (Buf) > 0) then --  Aceptamos un poner
               Primero (Cola_Poner_Pendiente, Rec_Chan);
               Borrar (Cola_Poner_Pendiente);
               Receive (Rec_Chan, Item);
               Insertar (Buf, Item);
            end if;

         end loop;
      end loop;
   exception
      when E : Name_Error =>
         Put ("Error en servidor de buffer:");
         Put_Line (Exception_Name (E));
   end BufServer;

   --  Variable que representa la tarea servidora
   TheBufServer : BufServer;

   --  Definición de los productores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Productor;
   task body Productor is
      Dato : Natural := 0;
      My_Channel : Channel;
      Name_Error : exception;
   begin
      Create (My_Channel);
      loop
         TheBufServer.Poner (My_Channel);
         Send (My_Channel, Dato);
         Put_Line ("Productor envió " & Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
         delay 0.05;
      end loop;
   exception
      when E : Name_Error =>
         Put ("Error en productor:");
         Put_Line (Exception_Name (E));
   end Productor;


   --  Definición de los consumidores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Consumidor;
   task body Consumidor is
      Dato : Natural := 0;
      My_Channel : Channel;
      Name_Error : exception;
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
   exception
      when E : Name_Error =>
         Put ("Error en consumidor:");
         Put_Line (Exception_Name (E));
   end Consumidor;


   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheConsumers : array (1 .. NCons) of Consumidor;

begin --  Principal
   null;
end Bb_Msg;
