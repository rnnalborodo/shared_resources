--  bbeo_msg.adb -- productor / servidor / consumidor con mensajes y
--  canales expl�citos.  El consumidor puede elegir entre consumir
--  pares o impares.
--
--  Author : MCL

--  El canal es un recurso separado, que empleamos para comunicar
--  tareas expl�citamente.
with Channels;

with Colas;

--  with ADA.Text_IO;
--  use ADA.Text_IO;

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Rv_Msg is


   --  N�mero de productores y consumidores
   NCons : constant Positive := 9;
   NProd : constant Positive := 4;

   type Request_Type is (Even, Odd);

   --  Un canal para transmitirnos enteros
   package Channel_Int is
      new Channels (Integer);
   use Channel_Int;

   package Colas_Chan_Int is
      new Colas (Channel);
   use Colas_Chan_Int;

   --  Definici�n del interfaz servidor del buffer
   task type BufServer is
      entry Poner (Item : in Integer);
      entry Tomar (Which_Type : in     Request_Type;
                   Canal : in out Channel);
   end BufServer;

   --  Cuerpo del servidor del buffer
   task body BufServer is

      --  Variables que implementan el buffer de 1 dato
      Hay_Dato : Boolean := False;
      Dato : Integer;

      --  Peticiones pendientes.  Se podr�an almacenar varias
      --  peticiones, pero con almacenar una es suficiente.
      Pendientes : array (Request_Type) of Colas_Chan_Int.Cola;

      --  Variables locales para usar en un momento determinado.
      Canal_Enviar : Channel;
      Poder_Servir : Request_Type;
   begin
      loop
         --  Bucle  infinito  esperando   por  una  petici�n,  que  es
         --  admitida  accediendo al buffer  externo.  La  �nica entry
         --  que tiene condici�n de  bloqueo es aquella que no depende
         --  de   los  par�metros   de  entrada   :   aqu�  utilizamos
         --  directamente la  guarda y el  paso de par�metros  que nos
         --  proporciona el rendez-vous.
         select
            when True =>
               --  Aceptamos  siempre  peticiones  de  retirar  y  las
               --  asociamos al tipo de  elemento que se desea retirar
               --  introduciendolas en una cola.
               accept Tomar (Which_Type : in     Request_Type;
                             Canal : in out Channel)
               do
                  Insertar (Pendientes (Which_Type), Canal);
               end Tomar;
         or
            --  Podemos poner siempre que  haya sitio.  Es posible que
            --  haya  alguna petici�n  bloqueada que  se  pueda servir
            --  ahora.  Como s�lo hay  un dato, s�lo podemos servir un
            --  tipo de peticiones en cada momento; es ese tipo el que
            --  guardamos  en Poder_Servir,  para no  recalcularlo m�s
            --  veces de lo que es necesario.
            when not Hay_Dato =>
               accept Poner (Item : in Integer) do
                  Hay_Dato := True;
                  Dato := Item;
                  Poder_Servir := Request_Type'Val (Dato mod 2);
               end Poner;
         end select;
         if Hay_Dato and then
           not Es_Vacia (Pendientes (Poder_Servir)) then
            Primero (Pendientes (Poder_Servir), Canal_Enviar);
            Borrar (Pendientes (Poder_Servir));
            Send (Canal_Enviar, Dato);
            Hay_Dato := False;
         end if;
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
         Put_Line ("Productor envi� " & Integer'Image (Dato));
         Dato := (Dato + 1) mod 17;
      end loop;
   end Productor;


   --  Definici�n de los consumidores; mandan mensajes directamente a la
   --  tarea que implementa el servidor
   task type Consumidor (Which_Type : Request_Type);
   task body Consumidor is
      Dato : Natural;
      My_Channel : Channel;
   begin
      Create (My_Channel);
      loop
         --  Pedimos que nos manden el dato, y decimos por qu�
         --  canal lo vamos a esperar
         TheBufServer.Tomar (Which_Type, My_Channel);
         Receive (My_Channel, Dato);
         Put_Line ("Consumidor obtuvo " & Integer'Image (Dato));
         delay 0.5;
      end loop;
   end Consumidor;


   --  Ahora se lanzan los clientes
   TheProducers : array (1 .. NProd) of Productor;
   TheEvenConsumers : array (1 .. NCons / 2) of Consumidor (Even);
   TheOddConsumers : array (1 .. NCons / 2) of Consumidor (Odd);

begin --  Principal
   null;
end Bb_Eo_Rv_Msg;
