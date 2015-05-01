--  multibuffer_msg.adb --  Multibuffer "destilado"
--
--  Author : Manuel Carro

--  with Ada.Text_Io;
--  use Ada.Text_Io;

with Conc_IO;
use Conc_IO;

with Channels;

with Ada.Numerics.Discrete_Random;

procedure Multibuffer_Msg is

   Num_Consumers : constant Positive := 8;
   Num_Producers : constant Positive := 4;

   --  The bounded buffer is a protected object with synchronization

   --  Constants and type definitions
   --  They cannot go into the object : only the state lives there!
   Buffer_Size : constant Natural := 10;

   --  A modular type gives a shorter and more readable code
   subtype Buffer_Quantity is Natural range 0 .. Buffer_Size;
   subtype Buffer_Range is Buffer_Quantity range 0 .. Buffer_Size - 1;


   --  Random generation of amounts of items to get or to put
   --  The maximum number of data which can be added to/retrieved from the
   --  array is Buffer_Size/2, in order to avoid interlocking.
   subtype Random_Range is
     Buffer_Range range 1 .. Buffer_Range (Buffer_Size / 2);

   package Random_Amount is
      new Ada.Numerics.Discrete_Random (Random_Range);
   use Random_Amount;

   type Ack_Message is (Void_Message);
   package Item_Channel is
      new Channels (Ack_Message);
   use Item_Channel;


   task type MultiBuffer is
      entry Get (Num_Items : in     Buffer_Quantity;
                 The_Get_Channel : in out Channel);
      entry Put (Num_Items : in     Buffer_Quantity;
                 The_Put_Channel : in out Channel);
   end MultiBuffer;

   task body MultiBuffer is

      --  Number of items currently in the array
      Item_Counter : Buffer_Quantity := 0;

      --  Variables for the two-phase lock
      Delayed_Get : Boolean := False;
      Delayed_Put : Boolean := False;
      Num_Items_To_Get : Buffer_Quantity := 0;   --  Avoid compiler warnings
      Num_Items_To_Put : Buffer_Quantity := 0;   --  Avoid compiler warnings
      Get_Channel : Channel;
      Put_Channel : Channel;

      --  This is just to receive a syncronization message
      Dummy_Var : Ack_Message;

      --  Note : we are servicing GETs and PUTs after every entry, which
      --  makes some code to be duplicated.  A better implementation
      --  would check all the requests _after_ the select loop.  Beware
      --  of starvation in that caso.  Also, bear in mind that with the
      --  assumed constraints among the size of the buffer and the
      --  amount of data the clients can request at a time, Delayed_Get
      --  and Delayed_Put cannot be both true simultaneously.

   begin
      loop
         select
            when not Delayed_Get =>
               accept Get (Num_Items : in  Buffer_Quantity;
                           The_Get_Channel : in out Channel)
               do
                  --  Save parameters (Num_Items is needed to test
                  --  precondition, Get_Channel is needed to answer the
                  --  client).
                  Num_Items_To_Get := Num_Items;
                  Get_Channel := The_Get_Channel;
                  --  Test precondition and set delay variable now.  If we
                  --  are here, that is because there is no other pending
                  --  call.
                  Delayed_Get := Item_Counter < Num_Items;
               end Get;
               --  We are done here; we have to decide based on the
               --  variables we have saved.
               if not Delayed_Get then
                  --  The operation can be serviced right now; use the
                  --  state we have just copied
                  Item_Counter := Item_Counter - Num_Items_To_Get;
                  Send (Get_Channel, Void_Message);
               end if;
               --  If there is a delayed put, check if it can be served
               --  right now
               if Delayed_Put and then
                 Num_Items_To_Put + Item_Counter <= Buffer_Size then
                  Receive (Put_Channel, Dummy_Var);
                  Item_Counter := Item_Counter + Num_Items_To_Put;
                  Delayed_Put := False;
               end if;
         or
            when not Delayed_Put =>
               accept Put (Num_Items : in     Buffer_Quantity;
                           The_Put_Channel : in out Channel)
               do
                  Num_Items_To_Put := Num_Items;
                  Put_Channel := The_Put_Channel;
                  Delayed_Put := Buffer_Size - Item_Counter < Num_Items;
               end Put;

               if not Delayed_Put then
                  Receive (Put_Channel, Dummy_Var);
                  Item_Counter := Item_Counter + Num_Items_To_Put;
               end if;

               --  Look for a pending get to service
               if Delayed_Get and then
                 Item_Counter >= Num_Items_To_Get then
                  Item_Counter := Item_Counter - Num_Items_To_Get;
                  Send (Get_Channel, Void_Message);
                  Delayed_Get := False;
               end if;
         end select;
      end loop;
   end MultiBuffer;


   Pool : MultiBuffer;

   --  Each producer and consumer is a task

   task type Producer_Type;
   task body Producer_Type is
      Num : Random_Range;
      G : Generator;
      Put_Channel : Channel;
   begin
      Reset (G);
      Create (Put_Channel);
      loop
         delay 2.0;
         --  Produce data (Items)
         Num := Random (G);
         Put_Line ("Producer generates " &
                   Random_Range'Image (Num) &
                   " items");
         --  Tell the server we want to put messages
         Pool.Put (Num, Put_Channel);
         --  Now, our request has been acepted (because there no other
         --  request pending).  When the request is accepted, the
         --  server receives and unblocks the next Send
         Send (Put_Channel, Void_Message);
         Put_Line ("Producer puts " & Random_Range'Image (Num) & " items");
      end loop;
   end Producer_Type;


   task type Consumer_Type;
   task body Consumer_Type is
      Num : Random_Range;
      G : Generator;
      Get_Channel : Channel;
      M : Ack_Message;
   begin
      Reset (G);
      Create (Get_Channel);
      loop
         delay 3.0;
         Num := Random (G);
         Put_Line ("Consumer wants " & Random_Range'Image (Num) & " items");
         Pool.Get (Num, Get_Channel);
         --  Again, the message has no meaning, it is just a
         --  syncronization token
         Receive (Get_Channel, M);
         Put_Line ("Consumer gets " & Random_Range'Image (Num) & " items");
      end loop;

   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers : array (1 .. Num_Consumers) of Consumer_Type;
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Multibuffer_Msg;

